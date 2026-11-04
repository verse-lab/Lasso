module

/-
  A system whose letters are carried by steps rather than by states.

  An atom like `taken(a)` — "the step being taken is an `a`-step" — is not a predicate of any state, so
  encoding it as one costs a factor of |actions| in reachable states. Here a successor entry carries the
  atoms its own step contributes, and the letter read at a step is the source state's atoms together with
  the step's own. The product built on top of this (`Product.lean`) keeps its state set
  `SysState × Nat` unchanged, so an edge atom costs no states at all.

  See `EdgeLabels.md` for the design and for why the alternatives (an action inside `SysState`, or a letter
  indexed by the endpoint pair) are unsound.

  Defines:
  - `LStep`, `LSys.Edge`: a labelled step, and a step read as an edge with both endpoints
  - `LSys.targets`, `LSys.totalize`: the underlying unlabelled graph, and the self-loop a terminal state gets
  - `LSys.unlabelled`: a system with no edge atoms, which is how every state-labelled caller is adapted
  - `LSys.letter`: the letter a step reads
  - `LSys.toSpec`: the labelled system as a `TOASpec`
  - `Sys.IsRun`: a run of a plain state-labelled system, the notion the transfer bridges connect to

  Proves:
  - `LSys.mem_totalize`, `LSys.targets_totalize`, `LSys.targets_unlabelled`: the totalized graph's steps, and
    that totalizing and forgetting the letters commute
  - `LSys.letter_empty`, `LSys.mem_letter`: what a step's letter contains
  - the four bridges that read a labelled statement back as a state-labelled one, used by every caller not
    yet converted: `LSys.toSpec_isRun_ofRun` and `LSys.isRun_of_toSpec_unlabelled` (runs, both ways),
    `LSys.valuation_ofRun` and `LSys.valuation_unlabelled` (the letters such a run reads are just the state
    labels), and `LSys.finiteReach_unlabelled` (the finiteness witness)
-/
public import LTLLib.LTL.Propositional
public import LTLLib.AbstractSpec.Reachability
public import LTLLib.AbstractSpec.Acceptance

public section

namespace LTLLib

/-- One labelled step: the atoms the step itself contributes, and the state it lands in. -/
abbrev LStep (α : Type u) (SysState : Type v) [BEq α] [Hashable α] := Std.HashSet α × SysState

/-- A run of a state-labelled system: it starts initial and steps along the totalized successors. The
letters play no part, which is why this is a bare predicate rather than a spec's `isRun`. -/
@[expose] def Sys.IsRun {SysState : Type v} (sysSucc : SysState → Array SysState) (sysInit : List SysState)
    (τ : Nat → SysState) : Prop :=
  τ 0 ∈ sysInit ∧ ∀ n, τ (n + 1) ∈ totalizeSucc sysSucc (τ n)

namespace LSys

variable {α : Type u} {SysState : Type v} [BEq α] [Hashable α]

/-! ## The labelled graph -/

/-- A step read as an edge: source, the letter the step contributes, target. -/
abbrev Edge (α : Type u) (SysState : Type v) [BEq α] [Hashable α] := SysState × LStep α SysState

/-- The underlying unlabelled successor function, which is what `FiniteReach` is stated against. -/
@[expose] def targets (sysSucc : SysState → Array (LStep α SysState)) : SysState → Array SysState :=
  fun s => (sysSucc s).map Prod.snd

/-- A system with no edge atoms: every step contributes the empty letter. Every state-labelled caller is
adapted through this, and every statement about one specializes through `toSpec_unlabelled_isRun_iff`. -/
@[expose] def unlabelled (sysSucc : SysState → Array SysState) : SysState → Array (LStep α SysState) :=
  -- PERF: the empty letter is bound once per call rather than written inside the mapped closure, where
  -- it would allocate a `HashSet` per successor. (It cannot be hoisted above `fun s` — the compiler
  -- eta-expands a function-returning definition to its full arity, so a `let` there would be re-entered
  -- anyway; see `EdgeLabels.md` §9.)
  fun s => let e : Std.HashSet α := ∅; (sysSucc s).map (fun t => (e, t))

/-- Give a terminal state a self-loop reading no edge atoms, so every state has a step, as Büchi semantics
over infinite words requires. A deadlocked state stutters and takes no action. -/
@[expose] def totalize (sysSucc : SysState → Array (LStep α SysState)) : SysState → Array (LStep α SysState) :=
  fun s => let ss := sysSucc s; if ss.isEmpty then #[((∅ : Std.HashSet α), s)] else ss

/-- A system presented as **one** callback: a state's steps and its own atoms, together.

This is the shape the product actually consumes. `getSuccessors` and friends each apply `sysSucc s` and
`sysLabel s` at the same `s` in the same expression, so a two-callback system forces whoever implements it
to compute `s`'s transitions twice — and on Veil that is a full `tr` walk each. Taking the pair as the
primitive makes "one walk per state" a fact about the *type*, so nothing has to be memoised and nothing
outside the kernel has to be trusted. `EdgeLabels.md` §15. -/
abbrev StepFn (α : Type u) (SysState : Type v) [BEq α] [Hashable α] :=
  SysState → Array (LStep α SysState) × Std.HashSet α

/-- `totalize` with the steps already in hand, so a caller holding `sysStep s` does not re-enter it. -/
@[expose] def totalizeAt (ss : Array (LStep α SysState)) (s : SysState) : Array (LStep α SysState) :=
  if ss.isEmpty then #[((∅ : Std.HashSet α), s)] else ss

theorem totalize_eq_totalizeAt (sysSucc : SysState → Array (LStep α SysState)) (s : SysState) :
    totalize sysSucc s = totalizeAt (sysSucc s) s := rfl

/-- The two-callback view of a fused one. Every bridge below is stated against this, and Lean's
definitional eta for structures makes `ofPair (fun s => ((f s).1, (f s).2)) = f` hold by `rfl`. -/
@[expose] def StepFn.succ (f : StepFn α SysState) : SysState → Array (LStep α SysState) := fun s => (f s).1

@[expose] def StepFn.label (f : StepFn α SysState) : SysState → Std.HashSet α := fun s => (f s).2

/-- The letter read on a step whose source contributes `base` and which itself contributes `L`. Taking the
source's atoms as a value rather than as `sysLabel` and a state lets a caller hoist `sysLabel s` out of its
loop over the steps leaving `s`, which matters when deciding a state's atoms is expensive. The `isEmpty`
guard keeps a system with no edge atoms allocation-free. -/
@[expose] def letter (base L : Std.HashSet α) : Std.HashSet α :=
  if L.isEmpty then base else base.union L

/-! ## Basic facts -/

theorem mem_totalize {sysSucc : SysState → Array (LStep α SysState)} {s : SysState}
    {st : LStep α SysState} :
    st ∈ totalize sysSucc s ↔
      (if (sysSucc s).isEmpty then st = ((∅ : Std.HashSet α), s) else st ∈ sysSucc s) := by
  unfold totalize
  dsimp only
  split <;> simp

theorem mem_totalize_of_mem {sysSucc : SysState → Array (LStep α SysState)} {s : SysState}
    {st : LStep α SysState} (h : st ∈ sysSucc s) : st ∈ totalize sysSucc s := by
  refine mem_totalize.mpr ?_
  split
  · next he => exact absurd h (by simp [Array.isEmpty_iff.mp he])
  · exact h

/-- Forgetting the letters commutes with totalizing, which is what lets a labelled system reuse the
unlabelled `FiniteReach` machinery. -/
theorem targets_totalize (sysSucc : SysState → Array (LStep α SysState)) :
    targets (totalize sysSucc) = totalizeSucc (targets sysSucc) := by
  funext s
  unfold targets totalize totalizeSucc
  dsimp only
  split
  · next he => simp [Array.isEmpty_iff.mp he]
  · next he =>
    have : ¬ ((sysSucc s).map Prod.snd).isEmpty = true := by
      simpa [Array.isEmpty_iff] using he
    simp [this]

theorem targets_unlabelled (sysSucc : SysState → Array SysState) :
    targets (unlabelled (α := α) sysSucc) = sysSucc := by
  funext s
  simp [targets, unlabelled, Array.map_map, Function.comp_def]

theorem mem_unlabelled {sysSucc : SysState → Array SysState} {s : SysState}
    {st : LStep α SysState} : st ∈ unlabelled (α := α) sysSucc s ↔ st.1 = ∅ ∧ st.2 ∈ sysSucc s := by
  simp only [unlabelled, Array.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨rfl, ht⟩
  · rintro ⟨h1, h2⟩; exact ⟨st.2, h2, by rw [← h1]⟩

/-- On a system with no edge atoms the letter is exactly the state label. -/
@[simp] theorem letter_empty (base : Std.HashSet α) : letter base ∅ = base := by
  simp [letter]

theorem mem_letter [LawfulBEq α] [LawfulHashable α] {base L : Std.HashSet α} {a : α} :
    a ∈ letter base L ↔ a ∈ base ∨ a ∈ L := by
  unfold letter
  split
  · next he =>
    refine ⟨Or.inl, ?_⟩
    rintro (h' | h')
    · exact h'
    · exact absurd h' (Std.HashSet.isEmpty_iff_forall_not_mem.mp he a)
  · simp only [Std.HashSet.union_eq, Std.HashSet.mem_iff_contains, Std.HashSet.contains_union,
      Bool.or_eq_true]

/-! ## The labelled system as an abstract spec -/

/-- The labelled system as a `TOASpec`: the letter sits on the edge, not on the state. -/
@[expose] def toSpec (sysSucc : SysState → Array (LStep α SysState)) (sysInit : List SysState)
    (sysLabel : SysState → Std.HashSet α) : TOASpec SysState (Edge α SysState) α 0 where
  src e := e.1
  dst e := e.2.2
  valid e := e.2 ∈ totalize sysSucc e.1
  initial s := s ∈ sysInit
  labelCompat e v := ∀ a, v a ↔ a ∈ letter (sysLabel e.1) e.2.1
  acceptMark := Fin.elim0

/-- The valuation a labelled run reads, position by position. -/
@[expose] def valuation (sysLabel : SysState → Std.HashSet α) (σ : Nat → Edge α SysState) : Nat → α → Prop :=
  fun i a => a ∈ letter (sysLabel (σ i).1) (σ i).2.1

theorem toSpec_isRun_iff (sysSucc : SysState → Array (LStep α SysState)) (sysInit : List SysState)
    (sysLabel : SysState → Std.HashSet α) (σ : Nat → Edge α SysState) :
    (toSpec sysSucc sysInit sysLabel).isRun σ ↔
      (σ 0).1 ∈ sysInit ∧ ∀ n, (σ n).2 ∈ totalize sysSucc (σ n).1 ∧ (σ n).2.2 = (σ (n + 1)).1 :=
  Iff.rfl

/-! ## Transfer from state-labelled systems

A system with no edge atoms is a labelled system whose runs are exactly the old ones, so a statement about
`Sys.IsRun` and a statement about `LSys.toSpec` say the same thing. Callers that have not yet been converted
go through this. -/

/-- The labelled run an unlabelled one induces: every step reads the empty letter. -/
@[expose] def ofRun (τ : Nat → SysState) : Nat → Edge α SysState :=
  fun n => (τ n, ((∅ : Std.HashSet α), τ (n + 1)))

@[simp] theorem valuation_ofRun (sysLabel : SysState → Std.HashSet α) (τ : Nat → SysState) :
    valuation sysLabel (ofRun (α := α) τ) = fun i a => a ∈ sysLabel (τ i) := by
  funext i a
  simp [valuation, ofRun]

/-- Every step of a system with no edge atoms reads the empty letter, the totalizing self-loop included. -/
theorem letter_eq_empty_of_unlabelled {sysSucc : SysState → Array SysState} {s : SysState}
    {st : LStep α SysState} (h : st ∈ totalize (unlabelled (α := α) sysSucc) s) :
    st.1 = ∅ := by
  have h' := mem_totalize.mp h
  split at h'
  · rw [h']
  · exact (mem_unlabelled.mp h').1

/-- Pointwise form: at every position, a run of an unlabelled system reads its source's label. This is the
bridge every state-labelled caller needs once a statement moves from `sysLabel (ρ n).1` to the letter. -/
theorem letter_of_isRun_unlabelled {sysSucc : SysState → Array SysState} {sysInit : List SysState}
    {sysLabel : SysState → Std.HashSet α} {ρ : Nat → Edge α SysState}
    (h : (toSpec (unlabelled sysSucc) sysInit sysLabel).isRun ρ) (n : Nat) :
    letter (sysLabel (ρ n).1) (ρ n).2.1 = sysLabel (ρ n).1 := by
  rw [letter_eq_empty_of_unlabelled (h.2 n).1, letter_empty]

/-- So a labelled run of such a system reads exactly the state labels, which is what lets a statement about
`LSys.toSpec` be read back as a statement about `Sys.IsRun`. -/
theorem valuation_unlabelled {sysSucc : SysState → Array SysState} {sysInit : List SysState}
    {sysLabel : SysState → Std.HashSet α} {σ : Nat → Edge α SysState}
    (h : (toSpec (unlabelled sysSucc) sysInit sysLabel).isRun σ) :
    valuation sysLabel σ = fun i a => a ∈ sysLabel (σ i).1 := by
  funext i a
  rw [valuation, letter_eq_empty_of_unlabelled (h.2 i).1, letter_empty]

/-- A state-labelled system's finiteness witness, read as the labelled system's. -/
theorem finiteReach_unlabelled {sysInit : List SysState} {sysSucc : SysState → Array SysState}
    (fr : FiniteReach sysInit sysSucc) :
    FiniteReach sysInit (targets (unlabelled (α := α) sysSucc)) := by
  rw [targets_unlabelled]; exact fr

/-- An ordinary run of a state-labelled system is a labelled run of the same system read as labelled. -/
theorem toSpec_isRun_ofRun {sysSucc : SysState → Array SysState} {sysInit : List SysState}
    {sysLabel : SysState → Std.HashSet α} {τ : Nat → SysState}
    (h : Sys.IsRun sysSucc sysInit τ) :
    (toSpec (unlabelled sysSucc) sysInit sysLabel).isRun (ofRun (α := α) τ) := by
  obtain ⟨hinit, hstep⟩ := h
  refine ⟨hinit, fun n => ⟨?_, rfl⟩⟩
  show ((∅ : Std.HashSet α), τ (n + 1)) ∈ totalize (unlabelled sysSucc) (τ n)
  have hmem : τ (n + 1) ∈ totalizeSucc sysSucc (τ n) := hstep n
  rw [totalizeSucc] at hmem
  split at hmem
  · next he =>
    have hemp : sysSucc (τ n) = #[] := Array.isEmpty_iff.mp he
    refine mem_totalize.mpr ?_
    rw [if_pos (by simp [unlabelled, hemp]), Array.mem_singleton.mp hmem]
  · exact mem_totalize_of_mem (mem_unlabelled.mpr ⟨rfl, hmem⟩)

/-- Forgetting the letters, a labelled run walks the underlying totalized graph. This is what a caller
running an unlabelled search — the feasibility fail-fast, say — needs from a labelled run. -/
theorem targets_of_isRun {sysSucc : SysState → Array (LStep α SysState)} {sysInit : List SysState}
    {sysLabel : SysState → Std.HashSet α} {ρ : Nat → Edge α SysState}
    (h : (toSpec sysSucc sysInit sysLabel).isRun ρ) (n : Nat) :
    (ρ (n + 1)).1 ∈ totalizeSucc (targets sysSucc) (ρ n).1 := by
  obtain ⟨hvalid, hlink⟩ := h.2 n
  have h2 : (ρ n).2.2 ∈ targets (totalize sysSucc) (ρ n).1 :=
    Array.mem_map.mpr ⟨(ρ n).2, hvalid, rfl⟩
  rw [targets_totalize] at h2
  have hlink' : (ρ n).2.2 = (ρ (n + 1)).1 := hlink
  rwa [hlink'] at h2

/-- Conversely, a labelled run of an unlabelled system projects to an ordinary run. -/
theorem isRun_of_toSpec_unlabelled {sysSucc : SysState → Array SysState} {sysInit : List SysState}
    {sysLabel : SysState → Std.HashSet α} {σ : Nat → Edge α SysState}
    (h : (toSpec (unlabelled sysSucc) sysInit sysLabel).isRun σ) :
    Sys.IsRun sysSucc sysInit (fun n => (σ n).1) := by
  obtain ⟨hinit, hstep⟩ := h
  refine ⟨hinit, fun n => ?_⟩
  obtain ⟨hvalid, hlink⟩ := hstep n
  show (σ (n + 1)).1 ∈ totalizeSucc sysSucc (σ n).1
  have h2 : (σ n).2.2 ∈ targets (totalize (unlabelled (α := α) sysSucc)) (σ n).1 :=
    Array.mem_map.mpr ⟨(σ n).2, hvalid, rfl⟩
  rw [targets_totalize, targets_unlabelled] at h2
  have hlink' : (σ n).2.2 = (σ (n + 1)).1 := hlink
  rwa [hlink'] at h2

/-! ## Predicates that cannot see a step's own atoms

A letter predicate used as a *region* — the `◇□ψ` part of a hoisted fairness — is well behaved exactly
when it cannot distinguish a step's letter from its source's label. Every predicate is `StateOnly` on an
unlabelled system, so this is a weakening of "the system has no edge atoms", and it is the hypothesis the
prune routes are proved under: see `EdgeLabels.md` §12.4 for why it is the right one and §12.1 for why
nothing weaker is affordable.

The point is that a `StateOnly` region behaves like a *state* region even on a labelled system, which is
what makes several regions jointly satisfiable as soon as they are separately satisfiable. Without it
that inference is NP-hard, which is the whole content of §12. -/

/-- `keep` cannot tell a step's own atoms from nothing: every step out of `s` reads a letter that `keep`
scores exactly as it scores `s`'s own label.

Note the quantifier is over *all* states and *all* their steps, including the totalizing self-loop, not
just the reachable ones — this is a property of the predicate against the system, established once. -/
@[expose] def StateOnly (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (keep : Std.HashSet α → Bool) : Prop :=
  ∀ s : SysState, ∀ st ∈ totalize sysSucc s, keep (letter (sysLabel s) st.1) = keep (sysLabel s)

/-- On a system with no edge atoms every predicate is `StateOnly`, so every statement proved under this
hypothesis specializes to the state-labelled callers. -/
theorem stateOnly_of_unlabelled (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (keep : Std.HashSet α → Bool) :
    StateOnly (unlabelled (α := α) sysSucc) sysLabel keep := by
  intro s st hst
  rw [letter_eq_empty_of_unlabelled hst, letter_empty]

/-- Closed under conjunction, which is what lets the *conjoined* region of several selected options
inherit the hypothesis from the options themselves. -/
theorem stateOnly_and {sysSucc : SysState → Array (LStep α SysState)}
    {sysLabel : SysState → Std.HashSet α} {k₁ k₂ : Std.HashSet α → Bool}
    (h₁ : StateOnly sysSucc sysLabel k₁) (h₂ : StateOnly sysSucc sysLabel k₂) :
    StateOnly sysSucc sysLabel (fun l => k₁ l && k₂ l) := by
  intro s st hst
  simp only []
  rw [h₁ s st hst, h₂ s st hst]

/-- Closed under an indexed conjunction, which is the form the prune's conjoined region takes: one
selected option per hoisted conjunct, `&&`-ed together. -/
theorem stateOnly_all {β : Type w} {sysSucc : SysState → Array (LStep α SysState)}
    {sysLabel : SysState → Std.HashSet α} {bs : List β} {f : β → Std.HashSet α → Bool}
    (h : ∀ b ∈ bs, StateOnly sysSucc sysLabel (f b)) :
    StateOnly sysSucc sysLabel (fun l => bs.all fun b => f b l) := by
  intro s st hst
  show (bs.all fun b => f b (letter (sysLabel s) st.1)) = (bs.all fun b => f b (sysLabel s))
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.all_cons]
    rw [h b (by simp) s st hst, ih fun c hc => h c (by simp [hc])]

/-- The constant-`true` region, which is what an option with no `◇□` part contributes. -/
theorem stateOnly_top (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) :
    StateOnly sysSucc sysLabel (fun _ => true) := fun _ _ _ => rfl

/-- A `StateOnly` region that holds at `s`'s label admits *every* step out of `s`. This is the form the
prune's proofs consume: it is what makes a region behave like a state region. -/
theorem mem_of_stateOnly {sysSucc : SysState → Array (LStep α SysState)}
    {sysLabel : SysState → Std.HashSet α} {keep : Std.HashSet α → Bool}
    (h : StateOnly sysSucc sysLabel keep) {s : SysState} (hs : keep (sysLabel s) = true)
    {st : LStep α SysState} (hst : st ∈ totalize sysSucc s) :
    keep (letter (sysLabel s) st.1) = true := by
  rw [h s st hst]; exact hs

/-! ### Discharging it syntactically

A caller does not reason about `StateOnly` semantically. It knows which atoms a *step* may contribute —
in Veil, exactly the indices of `T(…)` atoms — and checks that the region mentions none of them. -/

/-- No step ever contributes an atom the formula inspects. -/
@[expose] def NeverStepAtom (sysSucc : SysState → Array (LStep α SysState)) (b : BoolFormula α) : Prop :=
  ∀ s : SysState, ∀ st ∈ totalize sysSucc s, ∀ a ∈ b.atoms, a ∉ st.1

/-- The syntactic discharge. A step can only *add* atoms to the source's label (`letter` is a union), so if
none of the added atoms is one the formula looks at, the formula cannot tell the two apart. -/
theorem stateOnly_of_neverStepAtom [LawfulBEq α] [LawfulHashable α]
    {sysSucc : SysState → Array (LStep α SysState)} {sysLabel : SysState → Std.HashSet α}
    {b : BoolFormula α} (h : NeverStepAtom sysSucc b) :
    StateOnly sysSucc sysLabel b.eval := by
  intro s st hst
  refine BoolFormula.eval_congr fun a ha => ?_
  have hiff : a ∈ letter (sysLabel s) st.1 ↔ a ∈ sysLabel s := by
    rw [mem_letter]
    exact ⟨fun hmem => hmem.resolve_right (h s st hst a ha), Or.inl⟩
  simp only [Std.HashSet.mem_iff_contains] at hiff
  exact Bool.eq_iff_iff.mpr hiff

end LSys

end LTLLib
