module

/-
  Transition labels in disjunctive normal form, a disjunction of cubes of literals. LTL3BA's VWAA splitting and its
  `determinize` produce labels that are no longer a single cube, which is why LTL3BA uses BDDs (`[BKŘS12]` §5, §8).
  A cube list stays exact under conjunction, disjunction and sharp difference, and exports directly to `TGBA.Transition`,
  one non-contradictory cube per transition.

  `Cube.diffCube` is the literal-by-literal cube complement `e \ d = ⋃ᵢ (e ∧ l₁ ∧ ⋯ ∧ lᵢ₋₁ ∧ ¬lᵢ)` over the literals
  `l₁, …, lₖ` of `d`, the sharp operation of cube-based logic minimisation (Brayton, Hachtel, McMullen,
  Sangiovanni-Vincentelli, Logic Minimization Algorithms for VLSI Synthesis, `[SB00]`'s `[3]`). `DNF.diff` folds it over
  every cube of the right-hand side. Its semantic laws are proven directly, neither `[SB00]` nor `[BKŘS12]` states a
  correctness argument for it.

  Defines:
  - `hashSetEq`, `hashSetSubset`: set equality and inclusion on `Std.HashSet` by containment checks
  - `Cube`: a conjunction of literals as disjoint positive and negative atom sets
  - `Cube.sat`, `Cube.eval`: propositional and executable denotation
  - `Cube.isContradictory`: whether the cube denotes the empty set
  - `Cube.and`, `Cube.diffCube`: cube conjunction and the literal-by-literal complement split
  - `Cube.litImplies`: implication by literal inclusion, exact for a non-contradictory cube
  - `DNF`: a label as a list of cubes, read disjunctively
  - `DNF.sat`, `DNF.eval`, `DNF.top`, `DNF.bot`, `DNF.lit`, `DNF.and`, `DNF.or`, `DNF.diff`, `DNF.isEmpty`,
    `DNF.implies`, `DNF.cubes`
  - `DNF.impliesFast`: `DNF.implies` without allocating on two single cubes
  - `DNF.absorb`: absorption `c ∨ (c ∧ d) ≡ c`

  Proves:
  - `Cube.addLit_some_sat`, `Cube.addLit_none_unsat`: `addLit`'s effect and failure condition
  - `Cube.sat_go`, `Cube.sat_diffCube`: the sharp difference denotes `e ∧ ¬d`
  - `Cube.and_sat`, `Cube.sat_top`, `Cube.sat_lit`, `Cube.sat_literals`: the remaining `Cube` operations
  - `Cube.sat_of_litImplies`, `Cube.litImplies_of_sat_imp`, `DNF.sat_absorb`: literal inclusion is sound, and complete
    for non-contradictory cubes, absorption keeps the language
  - `DNF.sat_or`, `DNF.sat_and`, `DNF.sat_top`, `DNF.not_sat_bot`, `DNF.sat_lit`, `DNF.sat_diff`: the `DNF` operations
  - `DNF.isEmpty` and `DNF.implies` exact in both directions, `DNF.implies_iff`: `implies` is language inclusion
  - `DNF.impliesFast_eq`: the fast path computes `implies`
  - `DNF.sat_cubes`: a label's language is carried by the non-contradictory cubes it exports as transitions

  References:
  - `[BKŘS12]` Babiak, Křetínský, Řehák, Strejček. LTL to Büchi Automata Translation: Fast and More
    Deterministic. TACAS'12.
  - `[SB00]` Somenzi, Bloem. Efficient Büchi Automata from LTL Formulae. CAV'00.

  Sections:
  - Hash set comparisons
  - Cubes
  - Cube conjunction and complement
  - DNF labels
  - Semantic laws
-/
public import Std

public section

namespace Lasso

/-! ## Hash set comparisons -/

/-- `s1 = s2` by mutual containment. -/
@[expose] def hashSetEq {β : Type w} [BEq β] [Hashable β] (s1 s2 : Std.HashSet β) : Bool :=
  s1.all s2.contains && s2.all s1.contains

/-- `s1 ⊆ s2` by containment check. -/
@[expose] def hashSetSubset {β : Type w} [BEq β] [Hashable β] (s1 s2 : Std.HashSet β) : Bool :=
  s1.all s2.contains

theorem hashSetEq_iff {β} [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β] (s1 s2 : Std.HashSet β) :
    hashSetEq s1 s2 = true ↔ ∀ a, s1.contains a = true ↔ s2.contains a = true := by
  unfold hashSetEq
  simp only [Bool.and_eq_true, Std.HashSet.all_eq_true_iff_forall_mem, Std.HashSet.mem_iff_contains]
  exact ⟨fun ⟨h1, h2⟩ a => ⟨fun ha => h1 a ha, fun ha => h2 a ha⟩,
    fun h => ⟨fun a ha => (h a).mp ha, fun a ha => (h a).mpr ha⟩⟩

theorem hashSetSubset_iff {β} [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β] (s1 s2 : Std.HashSet β) :
    hashSetSubset s1 s2 = true ↔ ∀ a, s1.contains a = true → s2.contains a = true := by
  unfold hashSetSubset
  simp only [Std.HashSet.all_eq_true_iff_forall_mem, Std.HashSet.mem_iff_contains]

theorem hashSetSubset_trans {β} [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β]
    {s1 s2 s3 : Std.HashSet β} (h12 : hashSetSubset s1 s2 = true) (h23 : hashSetSubset s2 s3 = true) :
    hashSetSubset s1 s3 = true :=
  (hashSetSubset_iff s1 s3).mpr fun a ha => (hashSetSubset_iff s2 s3).mp h23 a ((hashSetSubset_iff s1 s2).mp h12 a ha)

theorem hashSetEq_of_subset_subset {β} [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β]
    {s1 s2 : Std.HashSet β} (h12 : hashSetSubset s1 s2 = true) (h21 : hashSetSubset s2 s1 = true) :
    hashSetEq s1 s2 = true :=
  (hashSetEq_iff s1 s2).mpr fun a => ⟨(hashSetSubset_iff s1 s2).mp h12 a, (hashSetSubset_iff s2 s1).mp h21 a⟩

theorem hashSetEq_refl {β} [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β] (s : Std.HashSet β) :
    hashSetEq s s = true := (hashSetEq_iff s s).mpr fun _ => Iff.rfl

/-! ## Cubes -/

/-- A conjunction of literals, positive and negative atoms kept apart as `TGBA.Transition` does. -/
structure Cube (α : Type u) [BEq α] [Hashable α] where
  pos : Std.HashSet α
  neg : Std.HashSet α

namespace Cube

variable {α : Type u} [BEq α] [Hashable α]

/-- Every positive atom holds and every negative atom fails. -/
@[expose] def sat (c : Cube α) (v : α → Prop) : Prop :=
  (∀ a, c.pos.contains a → v a) ∧ (∀ a, c.neg.contains a → ¬ v a)

/-- Executable denotation, the valuation given as the set of atoms that hold. -/
@[expose] def eval (c : Cube α) (v : Std.HashSet α) : Bool :=
  c.pos.toList.all v.contains && c.neg.toList.all fun a => !v.contains a

/-- Some atom is asserted both positively and negatively, so the cube denotes the empty set. -/
@[expose] def isContradictory (c : Cube α) : Bool :=
  c.pos.any c.neg.contains

/-- The cube with no constraints, denoting every valuation. -/
@[expose] def top : Cube α := { pos := Std.HashSet.emptyWithCapacity 0, neg := Std.HashSet.emptyWithCapacity 0 }

/-- The single positive or negative literal on `a`. -/
@[expose] def lit (a : α) (b : Bool) : Cube α :=
  if b then { pos := Std.HashSet.emptyWithCapacity 1 |>.insert a, neg := Std.HashSet.emptyWithCapacity 0 }
  else { pos := Std.HashSet.emptyWithCapacity 0, neg := Std.HashSet.emptyWithCapacity 1 |>.insert a }

/-! ## Cube conjunction and complement -/

/-- Conjoin two cubes by union of their literal sets. -/
@[expose] def and (c d : Cube α) : Cube α := { pos := c.pos ∪ d.pos, neg := c.neg ∪ d.neg }

/-- `c ⇒ d` by literal inclusion, `d`'s literals are all `c`'s. Exact whenever `c` is not contradictory. -/
@[expose] def litImplies (c d : Cube α) : Bool := hashSetSubset d.pos c.pos && hashSetSubset d.neg c.neg

/-- Add one literal to a cube, `none` when it contradicts a literal already there. -/
def addLit (c : Cube α) (a : α) (b : Bool) : Option (Cube α) :=
  if b then (if c.neg.contains a then none else some { c with pos := c.pos.insert a })
  else (if c.pos.contains a then none else some { c with neg := c.neg.insert a })

/-- `c`'s literals as `(atom, isPositive)` pairs. -/
@[expose] def literals (c : Cube α) : List (α × Bool) :=
  c.pos.toList.map (·, true) ++ c.neg.toList.map (·, false)

/-- `e \ d`, split into disjoint sub-cubes of `e`, one per literal of `d`: the sub-cube where every earlier
literal of `d` holds and this one is negated. -/
def diffCube (e d : Cube α) : List (Cube α) :=
  go e d.literals
where
  go (acc : Cube α) : List (α × Bool) → List (Cube α)
    | [] => []
    | (a, b) :: rest =>
      (match acc.addLit a !b with | some c => [c] | none => []) ++
      (match acc.addLit a b with | some c => go c rest | none => [])

end Cube

/-! ## DNF labels -/

/-- A label as a disjunction of cubes. -/
abbrev DNF (α : Type u) [BEq α] [Hashable α] := List (Cube α)

namespace DNF

variable {α : Type u} [BEq α] [Hashable α]

/-- Some cube of the disjunction is satisfied. -/
@[expose] def sat (x : DNF α) (v : α → Prop) : Prop := ∃ c ∈ x, Cube.sat c v

/-- Executable denotation, `Cube.eval` disjoined over the cubes. -/
@[expose] def eval (x : DNF α) (v : Std.HashSet α) : Bool := x.any (Cube.eval · v)

/-- The label denoting every valuation. -/
@[expose] def top : DNF α := [Cube.top]

/-- The label denoting no valuation. -/
@[expose] def bot : DNF α := []

/-- The single positive or negative literal on `a`. -/
@[expose] def lit (a : α) (b : Bool) : DNF α := [Cube.lit a b]

/-- Disjunction, list concatenation. -/
@[expose] def or (x y : DNF α) : DNF α := x ++ y

/-- Absorption, `c ∨ (c ∧ d) ≡ c`: drop every cube that implies (by `Cube.litImplies`) another kept cube. -/
def absorb (x : DNF α) : DNF α :=
  x.foldl (fun acc c => if acc.any c.litImplies then acc else (acc.filter fun d => !d.litImplies c) ++ [c]) []

/-- Conjunction, the pairwise cube conjunction of the disjuncts, contradictory products dropped and the rest absorbed. -/
@[expose] def and (x y : DNF α) : DNF α :=
  absorb (x.flatMap fun c => (y.map (Cube.and c)).filter fun d => !d.isContradictory)

/-- `c \ (⋃ y)`, folding `Cube.diffCube` over every cube of `y` in turn. -/
def diffCubeList (c : Cube α) (y : DNF α) : DNF α :=
  y.foldl (fun acc d => acc.flatMap (Cube.diffCube · d)) [c]

/-- Sharp difference, denoting `x ∧ ¬y`. -/
@[expose] def diff (x y : DNF α) : DNF α := x.flatMap fun c => diffCubeList c y

/-- Every cube is contradictory, which holds exactly when the label denotes no valuation. -/
@[expose] def isEmpty (x : DNF α) : Bool := x.all Cube.isContradictory

/-- `x` semantically implies `y`, `x ∧ ¬y` unsatisfiable, checked one cube of `x` at a time with an early exit. -/
@[expose] def implies (x y : DNF α) : Bool := x.all fun c => isEmpty (diffCubeList c y)

/-- `implies` without allocating on two single cubes, where a cube implies another exactly when it is contradictory or
asserts every literal of the other. -/
@[expose] def impliesFast (x y : DNF α) : Bool :=
  match x, y with
  | [c], [d] => c.isContradictory || c.litImplies d
  | x, y => implies x y

/-- The non-contradictory cubes of `x`, one per emitted `TGBA.Transition`. -/
@[expose] def cubes (x : DNF α) : List (Cube α) := x.filter fun c => !c.isContradictory

end DNF

/-! ## Semantic laws -/

namespace Cube

variable {α : Type u} [BEq α] [Hashable α]

/-- `addLit` fails exactly when the literal `(a, b)` contradicts what `c` already requires. -/
theorem addLit_none_unsat (c : Cube α) (a : α) (b : Bool) (h : c.addLit a b = none) (v : α → Prop) :
    ¬ (c.sat v ∧ (if b then v a else ¬ v a)) := by
  unfold addLit at h
  unfold sat
  grind

theorem sat_top (v : α → Prop) : (Cube.top (α := α)).sat v := by unfold Cube.top sat; grind

variable [LawfulBEq α]

/-- A contradictory cube is unsatisfiable. -/
theorem not_sat_of_isContradictory (c : Cube α) (h : c.isContradictory = true) (v : α → Prop) :
    ¬ c.sat v := by
  unfold isContradictory at h
  simp only [Std.HashSet.any_eq_true_iff_exists_mem, Std.HashSet.mem_iff_contains] at h
  unfold sat; grind

/-- A non-contradictory cube is realised by the valuation agreeing with its positive atoms. -/
theorem sat_of_not_isContradictory (c : Cube α) (h : c.isContradictory = false) :
    c.sat fun a => c.pos.contains a := by
  unfold isContradictory at h
  simp only [Std.HashSet.any_eq_false_iff_forall_mem, Std.HashSet.mem_iff_contains] at h
  unfold sat; grind

/-- A non-contradictory cube is also realised by the valuation excluding exactly its negative atoms. -/
theorem sat_of_not_isContradictory' (c : Cube α) (h : c.isContradictory = false) :
    c.sat fun a => ¬ c.neg.contains a := by
  unfold isContradictory at h
  simp only [Std.HashSet.any_eq_false_iff_forall_mem, Std.HashSet.mem_iff_contains] at h
  unfold sat; grind

/-- Two non-contradictory cubes with the same language have exactly the same literals. -/
theorem eq_of_mutual_sat_imp (c1 c2 : Cube α) (h1 : c1.isContradictory = false)
    (h2 : c2.isContradictory = false) (himp1 : ∀ v, c1.sat v → c2.sat v)
    (himp2 : ∀ v, c2.sat v → c1.sat v) :
    (∀ a, c1.pos.contains a ↔ c2.pos.contains a) ∧ (∀ a, c1.neg.contains a ↔ c2.neg.contains a) :=
  ⟨fun a => ⟨fun ha => (himp2 _ (sat_of_not_isContradictory c2 h2)).1 a ha,
      fun ha => (himp1 _ (sat_of_not_isContradictory c1 h1)).1 a ha⟩,
    fun a => ⟨fun ha => by simpa using (himp2 _ (sat_of_not_isContradictory' c2 h2)).2 a ha,
      fun ha => by simpa using (himp1 _ (sat_of_not_isContradictory' c1 h1)).2 a ha⟩⟩

/-- `sat` as a conjunction over `Cube.literals`. -/
theorem sat_literals (c : Cube α) (v : α → Prop) :
    c.sat v ↔ ∀ p ∈ c.literals, (if p.2 then v p.1 else ¬ v p.1) := by
  unfold sat literals
  simp only [List.mem_append, List.mem_map, Std.HashSet.mem_toList]
  constructor
  · rintro ⟨h1, h2⟩ p (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · simpa using h1 x hx
    · simpa using h2 x hx
  · intro h
    exact ⟨fun x hx => by simpa using h (x, true) (Or.inl ⟨x, hx, rfl⟩),
      fun x hx => by simpa using h (x, false) (Or.inr ⟨x, hx, rfl⟩)⟩

variable [LawfulHashable α]

/-- `addLit` extends the cube by exactly the literal `(a, b)`. -/
theorem addLit_some_sat (c : Cube α) (a : α) (b : Bool) (c' : Cube α) (h : c.addLit a b = some c')
    (v : α → Prop) : c'.sat v ↔ c.sat v ∧ (if b then v a else ¬ v a) := by
  unfold addLit at h
  unfold sat
  grind

theorem and_sat (c d : Cube α) (v : α → Prop) : (Cube.and c d).sat v ↔ c.sat v ∧ d.sat v := by
  unfold Cube.and sat
  simp only [Std.HashSet.contains_union, Bool.or_eq_true]
  grind

theorem litImplies_refl (c : Cube α) : c.litImplies c = true := by
  unfold litImplies
  simp [(hashSetSubset_iff _ _).mpr fun _ h => h]

theorem litImplies_trans {c1 c2 c3 : Cube α} (h12 : c1.litImplies c2 = true) (h23 : c2.litImplies c3 = true) :
    c1.litImplies c3 = true := by
  unfold litImplies at *
  simp only [Bool.and_eq_true] at *
  exact ⟨hashSetSubset_trans h23.1 h12.1, hashSetSubset_trans h23.2 h12.2⟩

/-- Literal inclusion is sound: every valuation of `c` satisfies `d`. -/
theorem sat_of_litImplies {c d : Cube α} (h : c.litImplies d = true) (v : α → Prop) (hv : c.sat v) : d.sat v := by
  unfold litImplies at h
  simp only [Bool.and_eq_true] at h
  exact ⟨fun a ha => hv.1 a ((hashSetSubset_iff _ _).mp h.1 a ha),
    fun a ha => hv.2 a ((hashSetSubset_iff _ _).mp h.2 a ha)⟩

/-- Literal inclusion is complete for a non-contradictory cube. -/
theorem litImplies_of_sat_imp {c d : Cube α} (hc : c.isContradictory = false) (h : ∀ v, c.sat v → d.sat v) :
    c.litImplies d = true := by
  unfold litImplies
  rw [Bool.and_eq_true, hashSetSubset_iff, hashSetSubset_iff]
  exact ⟨fun a ha => (h _ (sat_of_not_isContradictory c hc)).1 a ha,
    fun a ha => by simpa using (h _ (sat_of_not_isContradictory' c hc)).2 a ha⟩

theorem sat_lit (a : α) (b : Bool) (v : α → Prop) :
    (Cube.lit a b).sat v ↔ (if b then v a else ¬ v a) := by
  unfold Cube.lit sat; cases b <;> grind

/-- `diffCube.go acc rest` denotes `acc` with some literal of `rest` failing. -/
private theorem sat_go (acc : Cube α) (rest : List (α × Bool)) (v : α → Prop) :
    (∃ c' ∈ diffCube.go acc rest, c'.sat v) ↔
      acc.sat v ∧ ¬ (∀ p ∈ rest, (if p.2 then v p.1 else ¬ v p.1)) := by
  induction rest generalizing acc with
  | nil => simp [diffCube.go]
  | cons hd tl ih =>
    obtain ⟨a, b⟩ := hd
    have consToTl : (∀ p, p = (a, b) ∨ p ∈ tl → (if p.2 then v p.1 else ¬ v p.1)) →
        ∀ p ∈ tl, (if p.2 then v p.1 else ¬ v p.1) := fun h p hp => h p (Or.inr hp)
    have headHolds : (∀ p, p = (a, b) ∨ p ∈ tl → (if p.2 then v p.1 else ¬ v p.1)) →
        (if b then v a else ¬ v a) := fun h => h (a, b) (Or.inl rfl)
    have buildCons : (if b then v a else ¬ v a) → (∀ p ∈ tl, (if p.2 then v p.1 else ¬ v p.1)) →
        (∀ p, p = (a, b) ∨ p ∈ tl → (if p.2 then v p.1 else ¬ v p.1)) := by
      rintro hP htl p (rfl | hp)
      · exact hP
      · exact htl p hp
    rcases haddneg : acc.addLit a (!b) with _ | cneg <;>
      rcases haddpos : acc.addLit a b with _ | cpos <;>
      simp only [diffCube.go, haddneg, haddpos, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, false_or]
    · -- neither literal choice extends acc
      have h1 := addLit_none_unsat acc a (!b) haddneg v
      have h2 := addLit_none_unsat acc a b haddpos v
      constructor
      · rintro ⟨-, hf, -⟩; exact hf.elim
      · rintro ⟨hacc, -⟩
        have hcontra : (if b then v a else ¬ v a) :=
          Classical.byContradiction fun hP' => h1 ⟨hacc, by rcases b <;> simp_all⟩
        exact absurd ⟨hacc, hcontra⟩ h2
    · -- the negated literal fails to extend acc, the literal itself always extends it
      have h1 := addLit_none_unsat acc a (!b) haddneg v
      have hsat := addLit_some_sat acc a b cpos haddpos v
      have hih := ih cpos
      constructor
      · rintro ⟨c', hmem, hsat'⟩
        obtain ⟨hcpos, hnottl⟩ := hih.mp ⟨c', hmem, hsat'⟩
        obtain ⟨hacc, -⟩ := hsat.mp hcpos
        exact ⟨hacc, fun hcons => hnottl (consToTl hcons)⟩
      · rintro ⟨hacc, hnot⟩
        have hP : (if b then v a else ¬ v a) :=
          Classical.byContradiction fun hP' => h1 ⟨hacc, by rcases b <;> simp_all⟩
        exact hih.mpr ⟨hsat.mpr ⟨hacc, hP⟩, fun htl => hnot (buildCons hP htl)⟩
    · -- the literal fails to extend acc, its negation always extends it
      have h2 := addLit_none_unsat acc a b haddpos v
      have hsat := addLit_some_sat acc a (!b) cneg haddneg v
      constructor
      · rintro ⟨c', rfl, hsat'⟩
        obtain ⟨hacc, hnegb⟩ := hsat.mp hsat'
        refine ⟨hacc, fun hcons => ?_⟩
        have := headHolds hcons
        rcases b <;> simp_all
      · rintro ⟨hacc, -⟩
        exact ⟨cneg, rfl, hsat.mpr ⟨hacc, Classical.byContradiction fun hP' =>
          h2 ⟨hacc, by rcases b <;> simp_all⟩⟩⟩
    · -- both branches extend acc, the usual case
      have hsatn := addLit_some_sat acc a (!b) cneg haddneg v
      have hsatp := addLit_some_sat acc a b cpos haddpos v
      have hih := ih cpos
      constructor
      · rintro ⟨c', heq, hsat'⟩
        rcases heq with heq | hmem
        · subst heq
          obtain ⟨hacc, hnegb⟩ := hsatn.mp hsat'
          refine ⟨hacc, fun hcons => ?_⟩
          have := headHolds hcons
          rcases b <;> simp_all
        · obtain ⟨hcpos, hnottl⟩ := hih.mp ⟨c', hmem, hsat'⟩
          obtain ⟨hacc, -⟩ := hsatp.mp hcpos
          exact ⟨hacc, fun hcons => hnottl (consToTl hcons)⟩
      · rintro ⟨hacc, hnot⟩
        by_cases hP : (if b then v a else ¬ v a)
        · obtain ⟨c', hmem, hsat'⟩ := hih.mpr ⟨hsatp.mpr ⟨hacc, hP⟩, fun htl => hnot (buildCons hP htl)⟩
          exact ⟨c', Or.inr hmem, hsat'⟩
        · exact ⟨cneg, Or.inl rfl, hsatn.mpr ⟨hacc, by rcases b <;> simp_all⟩⟩

/-- The sharp difference, `e \ d`, denotes `e`'s valuations that are not `d`'s. -/
theorem sat_diffCube (e d : Cube α) (v : α → Prop) :
    (∃ c' ∈ diffCube e d, c'.sat v) ↔ e.sat v ∧ ¬ d.sat v := by
  unfold diffCube
  rw [sat_go, sat_literals d v]

end Cube

namespace DNF

variable {α : Type u} [BEq α] [Hashable α]

theorem sat_or (x y : DNF α) (v : α → Prop) : (or x y).sat v ↔ x.sat v ∨ y.sat v := by
  unfold or sat; grind

theorem not_sat_bot (v : α → Prop) : ¬ sat (bot (α := α)) v := by unfold bot sat; simp

/-- A singleton `DNF`'s language is exactly its one cube's. -/
theorem sat_singleton (c : Cube α) (v : α → Prop) : sat [c] v ↔ c.sat v := by
  unfold sat; simp

theorem sat_top (v : α → Prop) : sat (top (α := α)) v := ⟨Cube.top, List.mem_singleton_self _, Cube.sat_top v⟩

/-- `implies` is the emptiness of the whole sharp difference, computed cube by cube. -/
theorem implies_eq_isEmpty_diff (x y : DNF α) : implies x y = isEmpty (diff x y) := by
  unfold implies isEmpty diff
  rw [List.all_flatMap]

variable [LawfulBEq α]

/-- A label's language is carried by its non-contradictory cubes alone, the ones exported as transitions. -/
theorem sat_cubes (x : DNF α) (v : α → Prop) : (∃ c ∈ x.cubes, c.sat v) ↔ x.sat v := by
  unfold cubes sat
  constructor
  · rintro ⟨c, hc, hsat⟩
    exact ⟨c, (List.mem_filter.mp hc).1, hsat⟩
  · rintro ⟨c, hc, hsat⟩
    refine ⟨c, List.mem_filter.mpr ⟨hc, ?_⟩, hsat⟩
    cases hcon : c.isContradictory
    · rfl
    · exact absurd hsat (Cube.not_sat_of_isContradictory c hcon v)

/-- An `isEmpty` label is unsatisfiable. -/
theorem not_sat_of_isEmpty (x : DNF α) (h : isEmpty x = true) (v : α → Prop) : ¬ x.sat v := by
  unfold isEmpty at h
  rintro ⟨c, hc, hsat⟩
  exact Cube.not_sat_of_isContradictory c (List.all_eq_true.mp h c hc) v hsat

/-- A label that is not `isEmpty` is satisfiable. -/
theorem sat_of_not_isEmpty (x : DNF α) (h : isEmpty x = false) : ∃ v, x.sat v := by
  unfold isEmpty at h
  have hex : ∃ c ∈ x, c.isContradictory = false :=
    Classical.byContradiction fun hne =>
      absurd (List.all_eq_true.mpr fun c hc =>
        Classical.byContradiction fun hcf => hne ⟨c, hc, by simpa using hcf⟩) (by simp [h])
  obtain ⟨c, hc, hcontra⟩ := hex
  exact ⟨fun a => c.pos.contains a, c, hc, Cube.sat_of_not_isContradictory c hcontra⟩

variable [LawfulHashable α]

/-- Absorption keeps the language. -/
theorem sat_absorb (x : DNF α) (v : α → Prop) : (absorb x).sat v ↔ x.sat v := by
  unfold absorb
  suffices H : ∀ (l acc : DNF α), (l.foldl (fun acc c => if acc.any c.litImplies then acc
      else (acc.filter fun d => !d.litImplies c) ++ [c]) acc).sat v ↔ acc.sat v ∨ DNF.sat l v by
    rw [H]; simp [sat]
  intro l
  induction l with
  | nil => intro acc; simp [sat]
  | cons c l ih =>
    intro acc
    rw [List.foldl_cons, ih]
    have hcons : DNF.sat (c :: l) v ↔ c.sat v ∨ DNF.sat l v := by simp [sat]
    rw [hcons]
    split
    · rename_i hany
      obtain ⟨d, hd, hcd⟩ := List.any_eq_true.mp hany
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl h
        · exact Or.inl ⟨d, hd, Cube.sat_of_litImplies hcd v h⟩
        · exact Or.inr h
    · have hmem : ∀ d, d ∈ (acc.filter fun d => !d.litImplies c) ++ [c] ↔
          (d ∈ acc ∧ d.litImplies c = false) ∨ d = c := by
        intro d; simp [List.mem_append, List.mem_filter]
      constructor
      · rintro (⟨d, hd, hdv⟩ | h)
        · rcases (hmem d).mp hd with ⟨hd, -⟩ | rfl
          · exact Or.inl ⟨d, hd, hdv⟩
          · exact Or.inr (Or.inl hdv)
        · exact Or.inr (Or.inr h)
      · rintro (⟨d, hd, hdv⟩ | h | h)
        · cases hdc : d.litImplies c
          · exact Or.inl ⟨d, (hmem d).mpr (Or.inl ⟨hd, hdc⟩), hdv⟩
          · exact Or.inl ⟨c, (hmem c).mpr (Or.inr rfl), Cube.sat_of_litImplies hdc v hdv⟩
        · exact Or.inl ⟨c, (hmem c).mpr (Or.inr rfl), h⟩
        · exact Or.inr h

theorem sat_and (x y : DNF α) (v : α → Prop) : (and x y).sat v ↔ x.sat v ∧ y.sat v := by
  unfold and
  rw [sat_absorb]
  unfold sat
  constructor
  · rintro ⟨c', hc', hsat⟩
    simp only [List.mem_flatMap, List.mem_filter, List.mem_map] at hc'
    obtain ⟨c, hc, ⟨d, hd, rfl⟩, -⟩ := hc'
    exact ⟨⟨c, hc, (Cube.and_sat c d v).mp hsat |>.1⟩, ⟨d, hd, (Cube.and_sat c d v).mp hsat |>.2⟩⟩
  · rintro ⟨⟨c, hc, hcsat⟩, ⟨d, hd, hdsat⟩⟩
    have hsat := (Cube.and_sat c d v).mpr ⟨hcsat, hdsat⟩
    refine ⟨Cube.and c d, List.mem_flatMap.mpr ⟨c, hc, List.mem_filter.mpr ⟨List.mem_map.mpr ⟨d, hd, rfl⟩, ?_⟩⟩, hsat⟩
    cases hcon : (Cube.and c d).isContradictory
    · rfl
    · exact absurd hsat (Cube.not_sat_of_isContradictory _ hcon v)


theorem sat_lit (a : α) (b : Bool) (v : α → Prop) : (lit a b).sat v ↔ (if b then v a else ¬ v a) := by
  unfold DNF.lit sat; simp [Cube.sat_lit]


/-- Subtracting one cube `d` from every disjunct of `acc` at once. -/
theorem sat_flatMap_diffCube (acc : DNF α) (d : Cube α) (v : α → Prop) :
    sat (acc.flatMap (Cube.diffCube · d)) v ↔ acc.sat v ∧ ¬ d.sat v := by
  unfold sat
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨c', ⟨c, hc, hc'⟩, hsat⟩
    have := (Cube.sat_diffCube c d v).mp ⟨c', hc', hsat⟩
    exact ⟨⟨c, hc, this.1⟩, this.2⟩
  · rintro ⟨⟨c, hc, hcsat⟩, hnd⟩
    obtain ⟨c', hc', hsat⟩ := (Cube.sat_diffCube c d v).mpr ⟨hcsat, hnd⟩
    exact ⟨c', ⟨c, hc, hc'⟩, hsat⟩

/-- Subtracting every cube of `rest` from `acc` in turn. -/
theorem sat_foldl_diffCube (acc : DNF α) (rest : List (Cube α)) (v : α → Prop) :
    sat (rest.foldl (fun acc d => acc.flatMap (Cube.diffCube · d)) acc) v ↔
      acc.sat v ∧ ¬ (∃ d ∈ rest, d.sat v) := by
  induction rest generalizing acc with
  | nil => simp [sat]
  | cons d rest ih =>
    rw [List.foldl_cons, ih, sat_flatMap_diffCube]
    constructor
    · rintro ⟨⟨hacc, hnd⟩, hnrest⟩
      refine ⟨hacc, ?_⟩
      rintro ⟨d', hd', hd'sat⟩
      rw [List.mem_cons] at hd'
      rcases hd' with rfl | hd'
      · exact hnd hd'sat
      · exact hnrest ⟨d', hd', hd'sat⟩
    · rintro ⟨hacc, hnot⟩
      refine ⟨⟨hacc, fun hd => hnot ⟨d, List.mem_cons_self, hd⟩⟩, fun ⟨d', hd', hd'sat⟩ => ?_⟩
      exact hnot ⟨d', List.mem_cons_of_mem _ hd', hd'sat⟩

theorem sat_diffCubeList (c : Cube α) (y : DNF α) (v : α → Prop) :
    (diffCubeList c y).sat v ↔ c.sat v ∧ ¬ y.sat v := by
  unfold diffCubeList
  rw [sat_foldl_diffCube]
  unfold sat
  simp

/-- The sharp difference denotes `x ∧ ¬y`. -/
theorem sat_diff (x y : DNF α) (v : α → Prop) : (diff x y).sat v ↔ x.sat v ∧ ¬ y.sat v := by
  unfold DNF.diff sat
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨c', ⟨c, hc, hc'⟩, hsat⟩
    have := (sat_diffCubeList c y v).mp ⟨c', hc', hsat⟩
    exact ⟨⟨c, hc, this.1⟩, this.2⟩
  · rintro ⟨⟨c, hc, hcsat⟩, hny⟩
    obtain ⟨c', hc', hsat⟩ := (sat_diffCubeList c y v).mpr ⟨hcsat, hny⟩
    exact ⟨c', ⟨c, hc, hc'⟩, hsat⟩

/-- `implies` is exact, `x ⇒ y` iff every valuation satisfying `x` also satisfies `y`. -/
theorem implies_iff (x y : DNF α) : implies x y = true ↔ ∀ v, x.sat v → y.sat v := by
  rw [implies_eq_isEmpty_diff]
  constructor
  · intro h v hx
    refine Classical.byContradiction fun hy => ?_
    exact not_sat_of_isEmpty _ h v ((sat_diff x y v).mpr ⟨hx, hy⟩)
  · intro h
    refine Classical.byContradiction fun hne => ?_
    obtain ⟨v, hv⟩ := sat_of_not_isEmpty _ (by simpa using hne)
    obtain ⟨hx, hy⟩ := (sat_diff x y v).mp hv
    exact hy (h v hx)

/-- `implies` is reflexive. -/
theorem implies_refl (x : DNF α) : implies x x = true := (implies_iff x x).mpr fun _ hx => hx

/-- `implies` is transitive. -/
theorem implies_trans {x y z : DNF α} (hxy : implies x y = true) (hyz : implies y z = true) :
    implies x z = true :=
  (implies_iff x z).mpr fun v hv => (implies_iff y z).mp hyz v ((implies_iff x y).mp hxy v hv)

/-- `implies_iff` for two singleton `DNF`s. -/
theorem implies_singleton_iff (c1 c2 : Cube α) :
    implies [c1] [c2] = true ↔ ∀ v, c1.sat v → c2.sat v := by
  rw [implies_iff]; simp only [sat_singleton]

theorem impliesFast_eq (x y : DNF α) : impliesFast x y = implies x y := by
  unfold impliesFast
  split
  · rename_i c d
    rw [Bool.eq_iff_iff, implies_singleton_iff, Bool.or_eq_true]
    constructor
    · rintro (h | h) v hv
      · exact absurd hv (Cube.not_sat_of_isContradictory c h v)
      · exact Cube.sat_of_litImplies h v hv
    · intro h
      cases hc : c.isContradictory
      · exact Or.inr (Cube.litImplies_of_sat_imp hc h)
      · exact Or.inl rfl
  · rfl

end DNF
