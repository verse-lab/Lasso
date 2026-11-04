module

/-
  Well-founded DFS reachability over `Nat`-keyed adjacency. `closure` processes one frontier node at a time, and
  `remaining`, the hash set of candidate ids not yet discovered, gives the lexicographic measure
  `(remaining.size, frontier.length)`: every step either erases a newly found candidate or shrinks the frontier.

  Invariants of `closure`'s recursion (`closure_step`), for a state universe `U` closed under `succ`:
  - `H1`: `frontier ⊆ seen`
  - `H2`: `seen ⊆ U`
  - `H3`: `U ⊆ seen ∪ remaining`
  - `H4`: every state that has left `frontier` has had `succ` folded into `seen`

  Defines:
  - `dedupFilter`: a node's successors that are still candidates, each once
  - `closure`: the closure of `seen` under `succ`, restricted to a shrinking `remaining` candidate pool
  - `reachableFrom`: `closure` seeded from a list of start nodes, `remaining` the rest of `candidates`

  Proves:
  - `contains_foldl_erase`, `size_foldl_erase_lt`: erasing a list from a hash set, and the termination measure
  - `closure_mono`: `closure` only ever adds to `seen`
  - `closure_step`, `reachableFrom_closed`: the invariants above make the result closed under `succ`, given `candidates`
    covers the part of `U` outside `starts`
  - `closure_subset`, `reachableFrom_subset`, `reachableFrom_trans`: `reachableFrom` lies inside every closed set
    covering the starts, and composes

  Sections:
  - Erasing from the candidate pool
  - Closure
  - Reachability semantics
-/
public import Std

public section

namespace LTLLib

/-! ## Erasing from the candidate pool -/

/-- Erasing a list of keys keeps exactly the members outside the list. -/
theorem contains_foldl_erase (l : List Nat) (s : Std.HashSet Nat) (x : Nat) :
    (l.foldl (·.erase ·) s).contains x = true ↔ s.contains x = true ∧ x ∉ l := by
  induction l generalizing s with
  | nil => simp
  | cons a rest ih =>
    rw [List.foldl_cons, ih, Std.HashSet.contains_erase, List.mem_cons]
    grind

theorem size_foldl_erase_le (l : List Nat) (s : Std.HashSet Nat) : (l.foldl (·.erase ·) s).size ≤ s.size := by
  induction l generalizing s with
  | nil => exact Nat.le_refl _
  | cons a rest ih => exact Nat.le_trans (ih (s.erase a)) Std.HashSet.size_erase_le

/-- Erasing a list that contains one of the set's members strictly shrinks the set. -/
theorem size_foldl_erase_lt (l : List Nat) (s : Std.HashSet Nat) (x : Nat) (hx : x ∈ l) (hxs : s.contains x = true) :
    (l.foldl (·.erase ·) s).size < s.size := by
  induction l generalizing s with
  | nil => simp at hx
  | cons a rest ih =>
    rw [List.foldl_cons]
    by_cases hax : a = x
    · subst hax
      have hmem : a ∈ s := Std.HashSet.mem_iff_contains.mpr hxs
      have hpos : 0 < s.size := by
        rcases Nat.eq_zero_or_pos s.size with h0 | h0
        · have hempty : s.isEmpty = true := by rw [Std.HashSet.isEmpty_eq_size_eq_zero, h0]; rfl
          exact absurd hmem (Std.HashSet.isEmpty_iff_forall_not_mem.mp hempty a)
        · exact h0
      have hlt : (s.erase a).size < s.size := by
        rw [Std.HashSet.size_erase, if_pos hmem]
        omega
      exact Nat.lt_of_le_of_lt (size_foldl_erase_le rest _) hlt
    · have hxrest : x ∈ rest := by rcases List.mem_cons.mp hx with h | h; exact absurd h.symm hax; exact h
      have hxs' : (s.erase a).contains x = true := by rw [Std.HashSet.contains_erase]; simp [hax, hxs]
      exact Nat.lt_of_lt_of_le (ih (s.erase a) hxrest hxs') Std.HashSet.size_erase_le

/-! ## Closure -/

/-- The members of `l` satisfying `p`, deduplicated. -/
def dedupFilter (l : List Nat) (p : Nat → Bool) : List Nat := (Std.HashSet.ofList l).toList.filter p

theorem mem_dedupFilter {l : List Nat} {p : Nat → Bool} {x : Nat} : x ∈ dedupFilter l p ↔ x ∈ l ∧ p x = true := by
  unfold dedupFilter
  rw [List.mem_filter, Std.HashSet.mem_toList, Std.HashSet.mem_ofList, List.contains_iff_mem]

/-- The ids reachable from `frontier` through `succ`, added to `seen`, restricted to the candidate pool `remaining`. -/
@[expose] def closure (succ : Nat → List Nat) (seen : Std.HashSet Nat) (frontier : List Nat) (remaining : Std.HashSet Nat) :
    Std.HashSet Nat :=
  match frontier with
  | [] => seen
  | q :: qs =>
    let found := dedupFilter (succ q) fun f => remaining.contains f
    closure succ (found.foldl (·.insert ·) seen) (found ++ qs) (found.foldl (·.erase ·) remaining)
termination_by (remaining.size, frontier.length)
decreasing_by
  by_cases hfound : (dedupFilter (succ q) fun f => remaining.contains f) = []
  · rw [hfound]
    exact Prod.Lex.right _ (by simp)
  · left
    obtain ⟨x, hxmem⟩ := List.exists_mem_of_ne_nil _ hfound
    exact size_foldl_erase_lt _ remaining x hxmem (mem_dedupFilter.mp hxmem).2

/-- The closure of `starts` under `succ`, restricted to `candidates`. -/
@[expose] def reachableFrom (succ : Nat → List Nat) (starts candidates : List Nat) : Std.HashSet Nat :=
  closure succ (Std.HashSet.ofList starts) starts (starts.foldl (·.erase ·) (Std.HashSet.ofList candidates))

/-! ## Reachability semantics -/

/-- Folding `insert` over a list, in order, only ever adds to `seen`. -/
theorem foldl_insert_mono (l : List Nat) (seen : Std.HashSet Nat) (x : Nat) (hx : seen.contains x) :
    (l.foldl (·.insert ·) seen).contains x := by
  induction l generalizing seen with
  | nil => exact hx
  | cons a rest ih => exact ih (seen.insert a) (by rw [Std.HashSet.contains_insert]; simp [hx])

/-- Folding `insert` over a list adds exactly that list's members to `seen`. -/
theorem foldl_insert_contains_iff (l : List Nat) (seen : Std.HashSet Nat) (x : Nat) :
    (l.foldl (·.insert ·) seen).contains x ↔ x ∈ l ∨ seen.contains x := by
  induction l generalizing seen with
  | nil => simp
  | cons a rest ih =>
    rw [List.foldl_cons, ih (seen.insert a)]
    simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h.symm)
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

/-- `closure` only ever adds to `seen`, never removes from it. -/
theorem closure_mono (succ : Nat → List Nat) :
    ∀ (seen : Std.HashSet Nat) (frontier : List Nat) (remaining : Std.HashSet Nat) (x : Nat),
      seen.contains x → (closure succ seen frontier remaining).contains x := by
  intro seen frontier remaining
  induction seen, frontier, remaining using closure.induct succ with
  | case1 seen remaining => intro x hx; simp only [closure]; exact hx
  | case2 seen remaining q qs found ih =>
    intro x hx
    rw [closure]
    exact ih x (foldl_insert_mono found seen x hx)

/-- The invariants `H1` to `H4` of the file header make `closure`'s result closed under `succ`. -/
theorem closure_step (succ : Nat → List Nat) (U : Nat → Prop) (hclosed : ∀ p, U p → ∀ q ∈ succ p, U q) :
    ∀ (seen : Std.HashSet Nat) (frontier : List Nat) (remaining : Std.HashSet Nat),
      (∀ q ∈ frontier, seen.contains q) →
      (∀ x, seen.contains x → U x) →
      (∀ x, U x → seen.contains x ∨ remaining.contains x) →
      (∀ p, seen.contains p → p ∉ frontier → ∀ q ∈ succ p, seen.contains q) →
      ∀ p, (closure succ seen frontier remaining).contains p →
        ∀ q ∈ succ p, (closure succ seen frontier remaining).contains q := by
  intro seen frontier remaining
  induction seen, frontier, remaining using closure.induct succ with
  | case1 seen remaining =>
    intro _ h2 h3 h4 p hp q hq
    simp only [closure] at hp ⊢
    exact h4 p hp (List.not_mem_nil) q hq
  | case2 seen remaining q qs found ih =>
    intro h1 h2 h3 h4
    have hfound : found = dedupFilter (succ q) (fun f => remaining.contains f) := rfl
    let newSeen := found.foldl (·.insert ·) seen
    have hnewSeen : newSeen = found.foldl (·.insert ·) seen := rfl
    let newRemaining := found.foldl (·.erase ·) remaining
    have hnewRemaining : newRemaining = found.foldl (·.erase ·) remaining := rfl
    have hqSeen : seen.contains q := h1 q (List.mem_cons_self ..)
    have hfoundMem : ∀ x, x ∈ found → x ∈ succ q ∧ remaining.contains x := by
      intro x hx; rw [hfound] at hx; exact mem_dedupFilter.mp hx
    have hnewSeenContains : ∀ x, newSeen.contains x ↔ x ∈ found ∨ seen.contains x :=
      foldl_insert_contains_iff found seen
    have h1' : ∀ x ∈ found ++ qs, newSeen.contains x := by
      intro x hx
      rw [hnewSeenContains]
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (h1 x (List.mem_cons_of_mem _ hx))
    have h2' : ∀ x, newSeen.contains x → U x := by
      intro x hx
      rw [hnewSeenContains] at hx
      rcases hx with hx | hx
      · exact hclosed q (h2 q hqSeen) x (hfoundMem x hx).1
      · exact h2 x hx
    have h3' : ∀ x, U x → newSeen.contains x ∨ newRemaining.contains x := by
      intro x hx
      rcases h3 x hx with hs | hr
      · exact Or.inl (by rw [hnewSeenContains]; exact Or.inr hs)
      · by_cases hf : x ∈ found
        · exact Or.inl (by rw [hnewSeenContains]; exact Or.inl hf)
        · exact Or.inr (by rw [hnewRemaining, contains_foldl_erase]; exact ⟨hr, hf⟩)
    have h4' : ∀ p, newSeen.contains p → p ∉ found ++ qs → ∀ r ∈ succ p, newSeen.contains r := by
      intro p hp hpnot r hr
      rw [hnewSeenContains] at hp
      rcases hp with hp | hp
      · exact absurd (List.mem_append_left qs hp) hpnot
      · by_cases hpq : p = q
        · subst hpq
          rw [hnewSeenContains]
          by_cases hrf : r ∈ found
          · exact Or.inl hrf
          · have hrU : U r := hclosed p (h2 p hp) r hr
            rcases h3 r hrU with hrs | hrr
            · exact Or.inr hrs
            · exact absurd (by rw [hfound]; exact mem_dedupFilter.mpr ⟨hr, hrr⟩) hrf
        · have hpnotfrontier : p ∉ (q :: qs) := by
            intro hmem
            rcases List.mem_cons.mp hmem with rfl | hmem
            · exact hpq rfl
            · exact hpnot (List.mem_append_right found hmem)
          have := h4 p hp hpnotfrontier r hr
          rw [hnewSeenContains]
          exact Or.inr this
    intro p hp r hr
    rw [closure] at hp ⊢
    exact ih h1' h2' h3' h4' p hp r hr

/-- `reachableFrom` is closed under `succ` within the state universe `U`, given `U` is closed under `succ`
and `U \ starts ⊆ candidates`. -/
theorem reachableFrom_closed (succ : Nat → List Nat) (starts candidates : List Nat) (U : Nat → Prop)
    (hclosed : ∀ p, U p → ∀ q ∈ succ p, U q) (hstarts : ∀ x, x ∈ starts → U x)
    (hcov : ∀ x, U x → x ∈ starts ∨ x ∈ candidates) :
    ∀ p, (reachableFrom succ starts candidates).contains p →
      ∀ q ∈ succ p, (reachableFrom succ starts candidates).contains q := by
  unfold reachableFrom
  apply closure_step succ U hclosed
  · intro q hq; rw [Std.HashSet.contains_ofList]; exact List.contains_iff_mem.mpr hq
  · intro x hx
    rw [Std.HashSet.contains_ofList] at hx
    exact hstarts x (List.contains_iff_mem.mp hx)
  · intro x hx
    rcases hcov x hx with hx' | hx'
    · exact Or.inl (by rw [Std.HashSet.contains_ofList]; exact List.contains_iff_mem.mpr hx')
    · by_cases hxs : x ∈ starts
      · exact Or.inl (by rw [Std.HashSet.contains_ofList]; exact List.contains_iff_mem.mpr hxs)
      · refine Or.inr ((contains_foldl_erase _ _ x).mpr ⟨?_, hxs⟩)
        rw [Std.HashSet.contains_ofList]; exact List.contains_iff_mem.mpr hx'
  · intro p hp hpnot q hq
    exact absurd (List.contains_iff_mem.mp (by rwa [Std.HashSet.contains_ofList] at hp)) hpnot

/-- Every start state is reachable. -/
theorem starts_subset_reachableFrom (succ : Nat → List Nat) (starts candidates : List Nat) (x : Nat)
    (hx : x ∈ starts) : (reachableFrom succ starts candidates).contains x := by
  unfold reachableFrom
  apply closure_mono
  rw [Std.HashSet.contains_ofList]
  exact List.contains_iff_mem.mpr hx

/-- `closure`'s result lies inside any `succ`-closed predicate that already covers `seen`. -/
theorem closure_subset (succ : Nat → List Nat) (S : Nat → Prop) (hSclosed : ∀ x, S x → ∀ y ∈ succ x, S y) :
    ∀ (seen : Std.HashSet Nat) (frontier : List Nat) (remaining : Std.HashSet Nat),
      (∀ x ∈ frontier, seen.contains x) → (∀ x, seen.contains x → S x) →
      ∀ x, (closure succ seen frontier remaining).contains x → S x := by
  intro seen frontier remaining
  induction seen, frontier, remaining using closure.induct succ with
  | case1 seen remaining => intro _ hSseen x hx; simp only [closure] at hx; exact hSseen x hx
  | case2 seen remaining q qs found ih =>
    intro h1 hSseen x hx
    have hqSeen : seen.contains q := h1 q (List.mem_cons_self ..)
    have hfoundSub : ∀ y ∈ found, y ∈ succ q := by
      intro y hy
      have hfound : found = dedupFilter (succ q) fun f => remaining.contains f := rfl
      rw [hfound] at hy
      exact (mem_dedupFilter.mp hy).1
    have hnewSeenS : ∀ y, (found.foldl (·.insert ·) seen).contains y → S y := by
      intro y hy
      rw [foldl_insert_contains_iff] at hy
      rcases hy with hy | hy
      · exact hSclosed q (hSseen q hqSeen) y (hfoundSub y hy)
      · exact hSseen y hy
    have h1' : ∀ y ∈ found ++ qs, (found.foldl (·.insert ·) seen).contains y := by
      intro y hy
      rw [foldl_insert_contains_iff]
      rcases List.mem_append.mp hy with hy | hy
      · exact Or.inl hy
      · exact Or.inr (h1 y (List.mem_cons_of_mem _ hy))
    rw [closure] at hx
    exact ih h1' hnewSeenS x hx

/-- `reachableFrom`'s result lies inside any `succ`-closed predicate that already covers `starts`. -/
theorem reachableFrom_subset (succ : Nat → List Nat) (S : Nat → Prop)
    (hSclosed : ∀ x, S x → ∀ y ∈ succ x, S y) (starts candidates : List Nat) (hSstarts : ∀ x ∈ starts, S x) :
    ∀ x, (reachableFrom succ starts candidates).contains x → S x := by
  unfold reachableFrom
  apply closure_subset succ S hSclosed
  · intro q hq; rw [Std.HashSet.contains_ofList]; exact List.contains_iff_mem.mpr hq
  · intro x hx; rw [Std.HashSet.contains_ofList] at hx; exact hSstarts x (List.contains_iff_mem.mp hx)

/-- Reachability composes: whatever a reachable `p` reaches is reachable, under `reachableFrom_closed`'s premises. -/
theorem reachableFrom_trans (succ : Nat → List Nat) (U : Nat → Prop)
    (hclosed : ∀ p, U p → ∀ q ∈ succ p, U q) (starts candidates : List Nat)
    (hstarts : ∀ x ∈ starts, U x) (hcov : ∀ x, U x → x ∈ starts ∨ x ∈ candidates) (p : Nat)
    (hp : (reachableFrom succ starts candidates).contains p) (p' : Nat)
    (hp' : (reachableFrom succ [p] candidates).contains p') :
    (reachableFrom succ starts candidates).contains p' := by
  revert hp'
  apply reachableFrom_subset succ (fun x => (reachableFrom succ starts candidates).contains x)
  · exact reachableFrom_closed succ starts candidates U hclosed hstarts hcov
  · intro x hx; rw [List.mem_singleton] at hx; subst hx; exact hp

end LTLLib
