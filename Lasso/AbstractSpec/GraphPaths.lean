module

/-
  Generic `succs`-graph reachability, `PathTo` is a path through unblocked intermediates, and the `chain_*`
  lemmas convert between `PathTo` and its list-of-states witness.

  Key definitions:
  - `PathTo`

  Key theorems:
  - `chain_reaches`: an index-based chain gives a `PathTo` witness between its head and last element
  - `PathTo.toChain`: the converse, a `PathTo` witness unrolled into its explicit chain
  - `chain_closure`: a predicate closed under `succs` and holding at a chain's head holds along the whole chain
  - `PathTo.confine`: an unblocked path re-blocked by any predicate already holding on every successor
  - `PathTo.mono_succs`: a path survives widening the successor relation to any pointwise superset
  - `PathTo.snoc`: a path extends by one edge out of an unblocked endpoint
  - `PathTo.closed`: an unblocked path stays inside any predicate closed under `succs` and holding at the source

  Sections:
  - Paths
  - Chains
-/

public section
namespace Lasso

/-! ## Paths -/

/-- A non-empty path from `s` to `t` via `succs`, where every intermediate state (not `s` or `t`) satisfies `¬blocked`. -/
inductive PathTo (succs : State → Array State) (blocked : State → Prop) : State → State → Prop where
  -- t is a successor of s.
  | direct {s t : State} (ht : t ∈ succs s) : PathTo succs blocked s t
  -- Through an intermediate: s → mid →* t where mid is unblocked.
  | through {s mid t : State} (hmid : mid ∈ succs s) (hunblocked : ¬blocked mid)
    (h : PathTo succs blocked mid t) : PathTo succs blocked s t

/-- More blocking means fewer paths, contravariant in `blocked`. -/
theorem PathTo.weaken {succs : State → Array State} {blocked₁ blocked₂ : State → Prop} {s t : State}
    (h : PathTo succs blocked₂ s t) (hsub : ∀ x, blocked₁ x → blocked₂ x) : PathTo succs blocked₁ s t := by
  induction h with
  | direct ht => exact .direct ht
  | through hmid hunb _ ih => exact .through hmid (fun hb => hunb (hsub _ hb)) ih

/-- Unrestricted `PathTo` is transitive. -/
theorem PathTo.trans {State} {succs : State → Array State} {s t u : State}
    (h1 : PathTo succs (fun _ => False) s t) :
    PathTo succs (fun _ => False) t u → PathTo succs (fun _ => False) s u := by
  induction h1 with
  | direct ht => intro h2; exact .through ht (fun h => h) h2
  | through hmid _ _ ih => intro h2; exact .through hmid (fun h => h) (ih h2)

/-- An unblocked path where `P` holds on every `succs`-successor is also a path blocked by `¬ P`,
since `P` already holds at each of its intermediates. -/
theorem PathTo.confine {State} {succs : State → Array State} {P : State → Prop} {s t : State}
    (h : PathTo succs (fun _ => False) s t) (hP : ∀ {a b : State}, b ∈ succs a → P b) :
    PathTo succs (fun x => ¬ P x) s t := by
  induction h with
  | direct ht => exact .direct ht
  | through hmid _ _ ih => exact .through hmid (fun hnP => hnP (hP hmid)) ih

/-- A path survives widening the successor relation to any pointwise superset. -/
theorem PathTo.mono_succs {State} {succs₁ succs₂ : State → Array State} {blocked : State → Prop} {s t : State}
    (hsub : ∀ a b, b ∈ succs₁ a → b ∈ succs₂ a) (h : PathTo succs₁ blocked s t) : PathTo succs₂ blocked s t := by
  induction h with
  | direct ht => exact .direct (hsub _ _ ht)
  | through hmid hunb _ ih => exact .through (hsub _ _ hmid) hunb ih

/-- A path extends by one edge out of its endpoint when that endpoint is unblocked. -/
theorem PathTo.snoc {State} {succs : State → Array State} {blocked : State → Prop} {s t u : State}
    (h : PathTo succs blocked s t) (ht : ¬ blocked t) (hu : u ∈ succs t) : PathTo succs blocked s u := by
  revert ht hu
  induction h with
  | direct hmid => intro ht hu; exact .through hmid ht (.direct hu)
  | through hmid hunb _ ih => intro ht hu; exact .through hmid hunb (ih ht hu)

/-- An unblocked path stays inside any predicate `P` closed under `succs` and holding at the source. -/
theorem PathTo.closed {State} {succs : State → Array State} {P : State → Prop} {s t : State}
    (h : PathTo succs (fun _ => False) s t) (hPs : P s) (hclosed : ∀ x, P x → ∀ y ∈ succs x, P y) : P t := by
  induction h with
  | direct ht => exact hclosed _ hPs _ ht
  | through hmid _ _ ih => exact ih (hclosed _ hPs _ hmid)

/-! ## Chains -/

/-- A `succs`-chain list gives a `PathTo` (or an equality, if a singleton) between its head and last element. -/
theorem chain_reaches {State} {succs : State → Array State} (l : List State)
    (hchain : ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i]) :
    ∀ (hne : l ≠ []), l.head hne = l.getLast hne ∨ PathTo succs (fun _ => False) (l.head hne) (l.getLast hne) := by
  induction l with
  | nil => intro hne; exact absurd rfl hne
  | cons a t ih =>
    intro _
    cases t with
    | nil => left; rfl
    | cons b t' =>
      right
      have hab : b ∈ succs a := by
        have h0 := hchain 0 (by simp)
        simpa using h0
      have hchain_tail : ∀ i, (hi : i + 1 < (b :: t').length) →
          (b :: t')[i+1] ∈ succs (b :: t')[i] := by
        intro i hi
        have h1 := hchain (i + 1) (by simpa using hi)
        simpa using h1
      have hhead : (a :: b :: t').head (by simp) = a := rfl
      have hgetlast : (a :: b :: t').getLast (by simp) = (b :: t').getLast (by simp) :=
        List.getLast_cons (by simp)
      rw [hhead, hgetlast]
      rcases ih hchain_tail (by simp) with heq | hp
      · exact heq ▸ PathTo.direct hab
      · exact PathTo.trans (PathTo.direct hab) hp

/-- Dropping the last element of a `succs`-chain list leaves a `succs`-chain. -/
theorem chain_dropLast {State} {succs : State → Array State} (l : List State)
    (hchain : ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i]) :
    ∀ i, (hi : i + 1 < l.dropLast.length) → l.dropLast[i+1] ∈ succs l.dropLast[i] := by
  intro i hi
  have hi' : i + 1 < l.length := by
    have hlen := List.length_dropLast (xs := l)
    omega
  have e1 : l.dropLast[i] = l[i]'(by omega) := List.getElem_dropLast (by omega)
  have e2 : l.dropLast[i+1] = l[i+1]'hi' := List.getElem_dropLast (by omega)
  rw [e1, e2]
  exact hchain i hi'

/-- Appending a successor of a chain's last element to a `succs`-chain keeps it a `succs`-chain. -/
theorem chain_append_singleton {State} {succs : State → Array State} (l : List State) (x : State)
    (hchain : ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i])
    (hne : l ≠ []) (hedge : x ∈ succs (l.getLast hne)) :
    ∀ i, (hi : i + 1 < (l ++ [x]).length) → (l ++ [x])[i+1] ∈ succs (l ++ [x])[i] := by
  have hlen : (l ++ [x]).length = l.length + 1 := by simp
  intro i hi
  by_cases hlt : i + 1 < l.length
  · have e1 : (l ++ [x])[i] = l[i]'(by omega) := List.getElem_append_left (by omega)
    have e2 : (l ++ [x])[i+1] = l[i+1]'(by omega) := List.getElem_append_left (by omega)
    rw [e1, e2]
    exact hchain i (by omega)
  · have hi1 : i + 1 = l.length := by omega
    have e1 : (l ++ [x])[i] = l[i]'(by omega) := List.getElem_append_left (by omega)
    have e2 : (l ++ [x])[i+1] = x := by simp [hi1]
    rw [e1, e2]
    have hlast : l[i]'(by omega) = l.getLast hne := by
      rw [List.getLast_eq_getElem]
      congr 1
      omega
    rw [hlast]
    exact hedge

/-- Prepending a state with an edge into a chain-list's head keeps it a `succs`-chain. -/
theorem chain_cons {State} {succs : State → Array State} (a : State) (l : List State)
    (hne : l ≠ [])
    (hchain : ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i])
    (hedge : l.head hne ∈ succs a) :
    ∀ i, (hi : i + 1 < (a :: l).length) → (a :: l)[i+1] ∈ succs (a :: l)[i] := by
  intro i hi
  cases i with
  | zero => simpa [List.head_eq_getElem] using hedge
  | succ k =>
    have hk : k + 1 < l.length := by simpa using hi
    simpa using hchain k hk

/-- A predicate holding at a chain's head and closed under `succs` holds along the whole chain. -/
theorem chain_closure {State} {succs : State → Array State} {P : State → Prop} (l : List State)
    (hne : l ≠ []) (hP0 : P (l.head hne))
    (hchain : ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i])
    (hclosed : ∀ s t, P s → t ∈ succs s → P t) :
    ∀ i, (hi : i < l.length) → P (l[i]'hi) := by
  intro i
  induction i with
  | zero => intro hi; rwa [show l[0]'hi = l.head hne from (List.head_eq_getElem hne).symm]
  | succ i ih => intro hi; exact hclosed _ _ (ih (by omega)) (hchain i (by omega))

/-- The converse of `chain_reaches`, a `PathTo` proof unrolled into its explicit witnessing chain. -/
theorem PathTo.toChain {State} {succs : State → Array State} {blocked : State → Prop} {s t : State}
    (h : PathTo succs blocked s t) :
    ∃ l : List State, ∃ hne : l ≠ [], l.head hne = s ∧ l.getLast hne = t ∧
      ∀ i, (hi : i + 1 < l.length) → l[i + 1] ∈ succs (l[i]) := by
  induction h with
  | @direct s t ht =>
    refine ⟨[s, t], by simp, rfl, by simp, fun i hi => ?_⟩
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    simpa using ht
  | @through s mid t hmid _ _ ih =>
    obtain ⟨l, hne, hhead, hlast, hchain⟩ := ih
    exact ⟨s :: l, by simp, rfl, by simpa [List.getLast_cons hne] using hlast,
      chain_cons s l hne hchain (hhead ▸ hmid)⟩

private theorem chain_tail {State} {succs : State → Array State} (a : State) (l : List State)
    (hchain : ∀ i, (hi : i + 1 < (a :: l).length) → (a :: l)[i+1] ∈ succs (a :: l)[i]) :
    ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i] := by
  intro i hi
  have h := hchain (i + 1) (by simpa using hi)
  simpa using h

/-- Concatenating two `succs`-chains across a boundary edge gives a `succs`-chain over the concatenation. -/
theorem chain_append {State} {succs : State → Array State} (l1 l2 : List State)
    (hchain1 : ∀ i, (hi : i + 1 < l1.length) → l1[i+1] ∈ succs l1[i])
    (hchain2 : ∀ i, (hi : i + 1 < l2.length) → l2[i+1] ∈ succs l2[i])
    (hne1 : l1 ≠ []) (hne2 : l2 ≠ [])
    (hedge : l2.head hne2 ∈ succs (l1.getLast hne1)) :
    ∀ i, (hi : i + 1 < (l1 ++ l2).length) → (l1 ++ l2)[i+1] ∈ succs (l1 ++ l2)[i] := by
  induction l1 with
  | nil => exact absurd rfl hne1
  | cons a as ih =>
    cases as with
    | nil =>
      simp only [List.getLast_singleton] at hedge
      simpa using chain_cons a l2 hne2 hchain2 hedge
    | cons b bs =>
      have hasne : (b :: bs : List State) ≠ [] := by simp
      have hgetlast_eq : (a :: b :: bs).getLast (by simp) = (b :: bs).getLast hasne :=
        List.getLast_cons hasne
      rw [hgetlast_eq] at hedge
      have hchain_as : ∀ i, (hi : i + 1 < (b :: bs).length) →
          (b :: bs)[i+1] ∈ succs (b :: bs)[i] := chain_tail a (b :: bs) hchain1
      have hrec := ih hchain_as hasne hedge
      have hab : b ∈ succs a := by simpa using hchain1 0 (by simp)
      simpa using chain_cons a ((b :: bs) ++ l2) (by simp) hrec (by simpa using hab)

/-- A `take n` prefix of a `succs`-chain list is itself a `succs`-chain. -/
theorem chain_take {State} {succs : State → Array State} (l : List State) (n : Nat)
    (hchain : ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i]) :
    ∀ i, (hi : i + 1 < (l.take n).length) → (l.take n)[i+1] ∈ succs (l.take n)[i] := by
  intro i hi
  have hi' : i + 1 < l.length := by
    have hlen : (l.take n).length ≤ l.length := by simp only [List.length_take]; omega
    omega
  have e1 : (l.take n)[i] = l[i]'(by omega) := List.getElem_take
  have e2 : (l.take n)[i+1] = l[i+1]'hi' := List.getElem_take
  rw [e1, e2]
  exact hchain i hi'

/-- A `drop n` suffix of a `succs`-chain list is itself a `succs`-chain. -/
theorem chain_drop {State} {succs : State → Array State} (l : List State) (n : Nat)
    (hchain : ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i]) :
    ∀ i, (hi : i + 1 < (l.drop n).length) → (l.drop n)[i+1] ∈ succs (l.drop n)[i] := by
  intro i hi
  have hbound : n + i + 1 < l.length := by
    have hlen : (l.drop n).length = l.length - n := by simp
    omega
  have e1 : (l.drop n)[i] = l[n+i]'(by omega) := List.getElem_drop
  have e2 : (l.drop n)[i+1] = l[n+i+1]'hbound := List.getElem_drop
  rw [e1, e2]
  exact hchain (n + i) hbound

/-- The left part of an append-split `succs`-chain is itself a `succs`-chain. -/
theorem chain_append_left {State} {succs : State → Array State} (l a b : List State)
    (heq : l = a ++ b)
    (hchain : ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i]) :
    ∀ i, (hi : i + 1 < a.length) → a[i+1] ∈ succs a[i] := by
  subst heq
  induction a with
  | nil => simp
  | cons x xs ih =>
    intro i hi
    cases i with
    | zero =>
      have hxs0 : 0 < xs.length := by simpa using hi
      have h := hchain 0 (by simp only [List.length_cons, List.length_append]; omega)
      have e : (xs ++ b)[0]'(by simp; omega) = xs[0]'hxs0 := List.getElem_append_left hxs0
      simpa [e] using h
    | succ k =>
      have hk : k + 1 < xs.length := by simpa using hi
      exact ih (chain_tail x (xs ++ b) hchain) k hk

/-- The right part of an append-split `succs`-chain is itself a `succs`-chain. -/
theorem chain_append_right {State} {succs : State → Array State} (l a b : List State)
    (heq : l = a ++ b)
    (hchain : ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i]) :
    ∀ i, (hi : i + 1 < b.length) → b[i+1] ∈ succs b[i] := by
  subst heq
  induction a with
  | nil => simpa using hchain
  | cons x xs ih => exact ih (chain_tail x (xs ++ b) hchain)

/-- The chain's last edge, `l.getLast ∈ succs (l.dropLast.getLast)`. -/
theorem chain_getLast_edge {State} {succs : State → Array State} (l : List State)
    (hne : l ≠ []) (hne' : l.dropLast ≠ [])
    (hchain : ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i]) :
    l.getLast hne ∈ succs (l.dropLast.getLast hne') := by
  have hlen : l.dropLast.length ≥ 1 := List.length_pos_iff.mpr hne'
  have hlen2 : l.length ≥ 2 := by
    have := List.length_dropLast (xs := l)
    omega
  have hdlen : l.dropLast.length = l.length - 1 := List.length_dropLast (xs := l)
  have e1 : l.dropLast.getLast hne' = l[l.length - 2]'(by omega) := by
    rw [List.getLast_eq_getElem, List.getElem_dropLast]
    congr 1
    omega
  have e2 : l.getLast hne = l[l.length - 1]'(by omega) := List.getLast_eq_getElem ..
  rw [e1, e2]
  have hstep := hchain (l.length - 2) (by omega)
  simpa [show l.length - 2 + 1 = l.length - 1 from by omega] using hstep

/-- The edge across an append boundary, `b.head ∈ succs (a.getLast)`. -/
theorem chain_append_boundary {State} {succs : State → Array State} (l a b : List State)
    (heq : l = a ++ b) (ha : a ≠ []) (hb : b ≠ [])
    (hchain : ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i]) :
    b.head hb ∈ succs (a.getLast ha) := by
  subst heq
  induction a with
  | nil => exact absurd rfl ha
  | cons x xs ih =>
    cases xs with
    | nil =>
      have hbl : 0 < b.length := List.length_pos_iff.mpr hb
      have h0 := hchain 0 (by simp; omega)
      simpa [List.head_eq_getElem] using h0
    | cons y ys =>
      have hxsne : (y :: ys : List State) ≠ [] := by simp
      have hgetlast_eq : (x :: y :: ys).getLast (by simp) = (y :: ys).getLast hxsne := by
        simp [List.getLast_cons]
      rw [hgetlast_eq]
      exact ih hxsne (chain_tail x ((y :: ys) ++ b) hchain)

/-- Dropping a list's last element doesn't change its head, when both are still nonempty. -/
theorem head_dropLast_eq {α : Type u} (l : List α) (hne : l ≠ [])
    (hpne : l.dropLast ≠ []) : l.dropLast.head hpne = l.head hne := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a t =>
    cases t with
    | nil => exact absurd rfl hpne
    | cons b t' => rfl

/-- Appending to a nonempty list doesn't change its head. -/
theorem head_append_singleton_eq {α : Type u} (l : List α) (x : α) (hne : l ≠ []) :
    (l ++ [x]).head (by simp) = l.head hne := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a t => rfl

end Lasso
