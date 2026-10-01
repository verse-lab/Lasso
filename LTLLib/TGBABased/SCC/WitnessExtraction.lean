/-
  Rebuilding an explicit accepting cycle from a known-valid SCC candidate, shared by every `DFSOps` refinement. A
  refinement's own stack is no witness, a state can sit in e.g. Dijkstra's `live` stack without lying on a path to the
  closing back-edge once its branch has been backtracked out of. `buildCycleFrom` instead chains BFS's confined to a finite
  `domain`: each round finds the nearest state with an edge covering a still-uncovered mark, follows it, and repeats until
  every mark is covered, then closes back to the anchor, following [CDP05]'s accepting-run construction. The candidate
  need not be a maximal SCC, since any two members of an accepting subset are mutually reachable inside it.

  Defines:
  - `bfsFindPath`: level-order BFS shortest-path search, confined to `domain`
  - `pickMarkedNext`, `findAnyEdge`: the next qualifying edge out of a given state
  - `connector`, `buildCycleFrom`, `stitchCycleAt`: chain edges into one cycle anchored at a given state

  Proves:
  - `bfsFindPath_stem`: over a domain holding every reachable state, the BFS finds a stem to any reachable target
  - `stitchCycleAt_valid`: the built cycle is a real, domain-confined, mark-covering `succs`-cycle
  - `stitchCycleAt_toTAcceptingCycle`, `stitchCycleAt_toTAcceptingCycle'`: the built cycle and a stem form
    a `TAcceptingCycle`, the primed form allowing the cycle to live in a subgraph of the stem's

  References:
  - [CDP05] Couvreur, Duret-Lutz, Poitrenaud. On-the-Fly Emptiness Checks for Generalized Büchi Automata. SPIN 2005, §5.

  Sections:
  - BFS expansion step
  - Level-order BFS
  - Adaptive edge search and cycle stitching
-/
import Std
import Batteries.Data.List.Perm
import LTLLib.AbstractSpec.EmptinessCheck
import LTLLib.AbstractSpec.GraphPaths
import LTLLib.TGBABased.AbstractSpec.SCCTheory
import LTLLib.Tactic.Set

namespace LTLLib

variable {State : Type u} [BEq State] [Hashable State]

/-! ## BFS expansion step -/

/-- Keep `d` only if it is a new, `domain`-confined state. -/
private def collectNew (domain : Std.HashSet State) :
    Std.HashSet State → List (State × List State) →
      Std.HashSet State × List (State × List State)
  | visited, [] => (visited, [])
  | visited, (d, path) :: rest =>
    if visited.contains d then
      collectNew domain visited rest
    else if domain.contains d then
      let (visited', kept) := collectNew domain (visited.insert d) rest
      (visited', (d, path) :: kept)
    else
      collectNew domain visited rest

private theorem collectNew_visited_eq (domain : Std.HashSet State) (visited : Std.HashSet State)
    (d : State) (path : List State) (rest : List (State × List State))
    (h1 : visited.contains d = true) :
    collectNew domain visited ((d, path) :: rest) = collectNew domain visited rest := by
  conv => lhs; unfold collectNew
  rw [if_pos h1]

private theorem collectNew_new_eq (domain : Std.HashSet State) (visited : Std.HashSet State)
    (d : State) (path : List State) (rest : List (State × List State))
    (h1 : ¬ visited.contains d = true) (h2 : domain.contains d = true) :
    collectNew domain visited ((d, path) :: rest) =
      ((collectNew domain (visited.insert d) rest).1,
        (d, path) :: (collectNew domain (visited.insert d) rest).2) := by
  conv => lhs; unfold collectNew
  rw [if_neg h1, if_pos h2]

private theorem collectNew_outside_eq (domain : Std.HashSet State) (visited : Std.HashSet State)
    (d : State) (path : List State) (rest : List (State × List State))
    (h1 : ¬ visited.contains d = true) (h2 : ¬ domain.contains d = true) :
    collectNew domain visited ((d, path) :: rest) = collectNew domain visited rest := by
  conv => lhs; unfold collectNew
  rw [if_neg h1, if_neg h2]

private theorem collectNew_kept_subset_candidates (domain : Std.HashSet State)
    (visited : Std.HashSet State) (candidates : List (State × List State)) :
    ∀ p ∈ (collectNew domain visited candidates).2, p ∈ candidates := by
  induction candidates generalizing visited with
  | nil => simp [collectNew]
  | cons hd tl ih =>
    obtain ⟨d, path⟩ := hd
    by_cases h1 : visited.contains d = true
    · rw [collectNew_visited_eq domain visited d path tl h1]
      exact fun p hp => List.mem_cons_of_mem _ (ih visited p hp)
    · by_cases h2 : domain.contains d = true
      · rw [collectNew_new_eq domain visited d path tl h1 h2]
        intro p hp
        rcases List.mem_cons.mp hp with hp | hp
        · exact hp ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih (visited.insert d) p hp)
      · rw [collectNew_outside_eq domain visited d path tl h1 h2]
        exact fun p hp => List.mem_cons_of_mem _ (ih visited p hp)

private theorem collectNew_kept_subset_domain (domain : Std.HashSet State)
    (visited : Std.HashSet State) (candidates : List (State × List State)) :
    ∀ p ∈ (collectNew domain visited candidates).2, domain.contains p.1 := by
  induction candidates generalizing visited with
  | nil => simp [collectNew]
  | cons hd tl ih =>
    obtain ⟨d, path⟩ := hd
    by_cases h1 : visited.contains d = true
    · rw [collectNew_visited_eq domain visited d path tl h1]; exact ih visited
    · by_cases h2 : domain.contains d = true
      · rw [collectNew_new_eq domain visited d path tl h1 h2]
        intro p hp
        rcases List.mem_cons.mp hp with hp | hp
        · exact hp ▸ h2
        · exact ih (visited.insert d) p hp
      · rw [collectNew_outside_eq domain visited d path tl h1 h2]; exact ih visited

private theorem collectNew_kept_nil_contains_eq (domain : Std.HashSet State) (visited : Std.HashSet State)
    (candidates : List (State × List State)) (hempty : (collectNew domain visited candidates).2 = []) :
    ∀ x, (collectNew domain visited candidates).1.contains x → visited.contains x := by
  induction candidates generalizing visited with
  | nil => intro x hx; simpa [collectNew] using hx
  | cons hd tl ih =>
    obtain ⟨d, path⟩ := hd
    by_cases h1 : visited.contains d = true
    · rw [collectNew_visited_eq domain visited d path tl h1] at hempty ⊢
      exact ih visited hempty
    · by_cases h2 : domain.contains d = true
      · rw [collectNew_new_eq domain visited d path tl h1 h2] at hempty
        exact absurd hempty (List.cons_ne_nil _ _)
      · rw [collectNew_outside_eq domain visited d path tl h1 h2] at hempty ⊢
        exact ih visited hempty

section CollectNewSpec

variable [LawfulBEq State] [LawfulHashable State]

private theorem collectNew_visited_subset (domain : Std.HashSet State)
    (visited : Std.HashSet State) (candidates : List (State × List State)) :
    ∀ x, visited.contains x → (collectNew domain visited candidates).1.contains x := by
  induction candidates generalizing visited with
  | nil => intro x hx; simpa [collectNew] using hx
  | cons hd tl ih =>
    obtain ⟨d, path⟩ := hd
    intro x hx
    by_cases h1 : visited.contains d = true
    · rw [collectNew_visited_eq domain visited d path tl h1]; exact ih visited x hx
    · by_cases h2 : domain.contains d = true
      · rw [collectNew_new_eq domain visited d path tl h1 h2]
        exact ih (visited.insert d) x (by simp [hx])
      · rw [collectNew_outside_eq domain visited d path tl h1 h2]; exact ih visited x hx

private theorem collectNew_visited_eq_or_kept (domain : Std.HashSet State) (visited : Std.HashSet State)
    (candidates : List (State × List State)) :
    ∀ x, (collectNew domain visited candidates).1.contains x →
      visited.contains x ∨ ∃ p ∈ (collectNew domain visited candidates).2, p.1 = x := by
  induction candidates generalizing visited with
  | nil => intro x hx; left; simpa [collectNew] using hx
  | cons hd tl ih =>
    obtain ⟨d, path⟩ := hd
    intro x hx
    by_cases h1 : visited.contains d = true
    · rw [collectNew_visited_eq domain visited d path tl h1] at hx ⊢
      exact ih visited x hx
    · by_cases h2 : domain.contains d = true
      · rw [collectNew_new_eq domain visited d path tl h1 h2] at hx ⊢
        rcases ih (visited.insert d) x hx with hx' | ⟨p, hp, hpx⟩
        · simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hx'
          rcases hx' with rfl | hx'
          · exact Or.inr ⟨(d, path), List.mem_cons_self, rfl⟩
          · exact Or.inl hx'
        · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, hpx⟩
      · rw [collectNew_outside_eq domain visited d path tl h1 h2] at hx ⊢
        exact ih visited x hx

private theorem collectNew_domain_candidate_subset_visited (domain : Std.HashSet State)
    (visited : Std.HashSet State) (candidates : List (State × List State)) :
    ∀ p ∈ candidates, domain.contains p.1 → (collectNew domain visited candidates).1.contains p.1 := by
  induction candidates generalizing visited with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨d, path⟩ := hd
    intro p hp hpdom
    rcases List.mem_cons.mp hp with rfl | hp
    · by_cases h1 : visited.contains d = true
      · rw [collectNew_visited_eq domain visited d path tl h1]
        exact collectNew_visited_subset domain visited tl d h1
      · rw [collectNew_new_eq domain visited d path tl h1 hpdom]
        exact collectNew_visited_subset domain (visited.insert d) tl d (by simp)
    · by_cases h1 : visited.contains d = true
      · rw [collectNew_visited_eq domain visited d path tl h1]; exact ih visited p hp hpdom
      · by_cases h2 : domain.contains d = true
        · rw [collectNew_new_eq domain visited d path tl h1 h2]
          exact ih (visited.insert d) p hp hpdom
        · rw [collectNew_outside_eq domain visited d path tl h1 h2]; exact ih visited p hp hpdom

private theorem collectNew_subset_domain (domain : Std.HashSet State)
    (visited : Std.HashSet State) (candidates : List (State × List State))
    (hvd : ∀ x, visited.contains x → domain.contains x) :
    ∀ x, (collectNew domain visited candidates).1.contains x → domain.contains x := by
  induction candidates generalizing visited with
  | nil => intro x hx; exact hvd x (by simpa [collectNew] using hx)
  | cons hd tl ih =>
    obtain ⟨d, path⟩ := hd
    by_cases h1 : visited.contains d = true
    · rw [collectNew_visited_eq domain visited d path tl h1]; exact ih visited hvd
    · by_cases h2 : domain.contains d = true
      · have hvd' : ∀ x, (visited.insert d).contains x → domain.contains x := by
          intro x hx
          simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hx
          rcases hx with rfl | hx
          · exact h2
          · exact hvd x hx
        rw [collectNew_new_eq domain visited d path tl h1 h2]
        exact ih (visited.insert d) hvd'
      · rw [collectNew_outside_eq domain visited d path tl h1 h2]; exact ih visited hvd

private theorem collectNew_size_eq (domain : Std.HashSet State)
    (visited : Std.HashSet State) (candidates : List (State × List State)) :
    (collectNew domain visited candidates).1.size =
      visited.size + (collectNew domain visited candidates).2.length := by
  induction candidates generalizing visited with
  | nil => simp [collectNew]
  | cons hd tl ih =>
    obtain ⟨d, path⟩ := hd
    by_cases h1 : visited.contains d = true
    · rw [collectNew_visited_eq domain visited d path tl h1]; exact ih visited
    · by_cases h2 : domain.contains d = true
      · have hins : (visited.insert d).size = visited.size + 1 := by
          rw [Std.HashSet.size_insert,
            if_neg (fun hmem => h1 (Std.HashSet.mem_iff_contains.mp hmem))]
        have hrec := ih (visited.insert d)
        rw [collectNew_new_eq domain visited d path tl h1 h2]
        simp only [List.length_cons]
        omega
      · rw [collectNew_outside_eq domain visited d path tl h1 h2]; exact ih visited

end CollectNewSpec

/-- A valid `succs`-chain, confined to `domain`, from some element of `starts` to `tgt`. -/
private def ValidChain (domain : Std.HashSet State) (succs : State → Array State)
    (starts : List State) (l : List State) (tgt : State) : Prop :=
  ∃ hne : l ≠ [], l.head hne ∈ starts ∧ l.getLast hne = tgt ∧ (∀ x ∈ l, domain.contains x) ∧
    ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i]

private theorem ValidChain.singleton {domain : Std.HashSet State} {succs : State → Array State}
    {starts : List State} {s : State} (hs : s ∈ starts) (hdom : domain.contains s) :
    ValidChain domain succs starts [s] s :=
  ⟨by simp, by simpa using hs, by simp, by simpa using hdom, by simp⟩

private theorem ValidChain.extend {domain : Std.HashSet State} {succs : State → Array State}
    {starts : List State} {l : List State} {cur d : State}
    (h : ValidChain domain succs starts l cur) (hd : d ∈ succs cur) (hdom : domain.contains d) :
    ValidChain domain succs starts (l ++ [d]) d := by
  obtain ⟨hne, hhead, hlast, hconf, hchain⟩ := h
  refine ⟨by simp, ?_, by simp, ?_, chain_append_singleton l d hchain hne (hlast ▸ hd)⟩
  · rw [head_append_singleton_eq l d hne]; exact hhead
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hconf x hx
    · rw [List.mem_singleton] at hx; rw [hx]; exact hdom

/-- One BFS level: every not-yet-visited, `domain`-confined successor of any `frontier` state, paired with the reversed
path taken to reach it. -/
private def bfsExpandLevel (domain : Std.HashSet State) (succs : State → Array State)
    (visited : Std.HashSet State) (frontier : List (State × List State)) :
    Std.HashSet State × List (State × List State) :=
  collectNew domain visited
    (frontier.flatMap fun (cur, revPath) => (succs cur).toList.map fun d => (d, d :: revPath))

private theorem bfsExpandLevel_kept_nil_visited_eq (domain : Std.HashSet State) (succs : State → Array State)
    (visited : Std.HashSet State) (frontier : List (State × List State))
    (hempty : (bfsExpandLevel domain succs visited frontier).2 = []) :
    ∀ x, (bfsExpandLevel domain succs visited frontier).1.contains x → visited.contains x :=
  collectNew_kept_nil_contains_eq domain visited _ hempty

section BfsExpandLevelSpec

variable [LawfulBEq State] [LawfulHashable State]

private theorem bfsExpandLevel_visited_subset (domain : Std.HashSet State)
    (succs : State → Array State) (visited : Std.HashSet State)
    (frontier : List (State × List State)) :
    ∀ x, visited.contains x → (bfsExpandLevel domain succs visited frontier).1.contains x :=
  collectNew_visited_subset domain visited _

private theorem bfsExpandLevel_subset_domain (domain : Std.HashSet State)
    (succs : State → Array State) (visited : Std.HashSet State)
    (frontier : List (State × List State))
    (hvd : ∀ x, visited.contains x → domain.contains x) :
    ∀ x, (bfsExpandLevel domain succs visited frontier).1.contains x → domain.contains x :=
  collectNew_subset_domain domain visited _ hvd

private theorem bfsExpandLevel_size_eq (domain : Std.HashSet State)
    (succs : State → Array State) (visited : Std.HashSet State)
    (frontier : List (State × List State)) :
    (bfsExpandLevel domain succs visited frontier).1.size =
      visited.size + (bfsExpandLevel domain succs visited frontier).2.length :=
  collectNew_size_eq domain visited _

private theorem bfsExpandLevel_closes_frontier (domain : Std.HashSet State) (succs : State → Array State)
    (visited : Std.HashSet State) (frontier : List (State × List State)) :
    ∀ q ∈ frontier, ∀ y ∈ succs q.1, domain.contains y →
      (bfsExpandLevel domain succs visited frontier).1.contains y := by
  intro q hq y hy hydom
  apply collectNew_domain_candidate_subset_visited domain visited _ (y, y :: q.2) _ hydom
  exact List.mem_flatMap.mpr ⟨q, hq, List.mem_map.mpr ⟨y, by simpa using hy, rfl⟩⟩

private theorem bfsExpandLevel_visited_eq_or_kept (domain : Std.HashSet State) (succs : State → Array State)
    (visited : Std.HashSet State) (frontier : List (State × List State)) :
    ∀ x, (bfsExpandLevel domain succs visited frontier).1.contains x →
      visited.contains x ∨ ∃ p ∈ (bfsExpandLevel domain succs visited frontier).2, p.1 = x :=
  collectNew_visited_eq_or_kept domain visited _

private theorem bfsExpandLevel_kept_subset_visited (domain : Std.HashSet State) (succs : State → Array State)
    (visited : Std.HashSet State) (frontier : List (State × List State)) :
    ∀ p ∈ (bfsExpandLevel domain succs visited frontier).2,
      (bfsExpandLevel domain succs visited frontier).1.contains p.1 := by
  intro p hp
  exact collectNew_domain_candidate_subset_visited domain visited _ p
    (collectNew_kept_subset_candidates domain visited _ p hp)
    (collectNew_kept_subset_domain domain visited _ p hp)

end BfsExpandLevelSpec

private theorem PathTo.mem_of_closed {domain : Std.HashSet State} {succs : State → Array State}
    {V : Std.HashSet State} {s t : State}
    (h : PathTo succs (fun x => ¬ domain.contains x) s t)
    (hclosed : ∀ x y, V.contains x → y ∈ succs x → domain.contains y → V.contains y) :
    V.contains s → domain.contains t → V.contains t := by
  induction h with
  | @direct s t ht => intro hs hdt; exact hclosed s t hs ht hdt
  | @through s mid t hmid hunblocked _ ih =>
    intro hs hdt
    have hdmid : domain.contains mid := by by_contra hc; exact hunblocked hc
    exact ih (hclosed s mid hs hmid hdmid) hdt

private theorem bfsExpandLevel_kept_extends (domain : Std.HashSet State) (succs : State → Array State)
    (visited : Std.HashSet State) (frontier : List (State × List State)) :
    ∀ p ∈ (bfsExpandLevel domain succs visited frontier).2,
      ∃ q ∈ frontier, p.1 ∈ succs q.1 ∧ p.2 = p.1 :: q.2 ∧ domain.contains p.1 := by
  intro p hp
  have hdomp : domain.contains p.1 := collectNew_kept_subset_domain domain visited _ p hp
  have hp' := collectNew_kept_subset_candidates domain visited _ p hp
  obtain ⟨q, hq, hp'⟩ := List.mem_flatMap.mp hp'
  obtain ⟨d, hd, heq⟩ := List.mem_map.mp hp'
  have hdmem : d ∈ succs q.1 := by simpa using hd
  exact ⟨q, hq, heq ▸ hdmem, by rw [← heq], hdomp⟩

private theorem bfsExpandLevel_kept_valid (domain : Std.HashSet State) (succs : State → Array State)
    (starts : List State) (visited : Std.HashSet State) (frontier : List (State × List State))
    (hfrontier : ∀ q ∈ frontier, ValidChain domain succs starts q.2.reverse q.1) :
    ∀ p ∈ (bfsExpandLevel domain succs visited frontier).2, ValidChain domain succs starts p.2.reverse p.1 := by
  intro p hp
  obtain ⟨q, hq, hedge, hpath, hdom⟩ := bfsExpandLevel_kept_extends domain succs visited frontier p hp
  have hext := (hfrontier q hq).extend hedge hdom
  rw [hpath, List.reverse_cons]
  exact hext

/-! ## Level-order BFS -/

section Bfs

variable [LawfulBEq State] [LawfulHashable State]

private theorem size_le_of_confined (domain visited : Std.HashSet State)
    (hvd : ∀ x, visited.contains x → domain.contains x) : visited.size ≤ domain.size := by
  have hnodupV : visited.toList.Nodup :=
    (Std.HashSet.distinct_toList (m := visited)).imp (fun {a b} h => by simpa [beq_iff_eq] using h)
  have hsub : visited.toList ⊆ domain.toList := fun x hx =>
    (Std.HashSet.mem_toList (m := domain)).mpr
      (Std.HashSet.mem_iff_contains.mpr (hvd x ((Std.HashSet.mem_iff_contains).mp
        ((Std.HashSet.mem_toList (m := visited)).mp hx))))
  have hlen := (List.subperm_of_subset hnodupV hsub).length_le
  rwa [Std.HashSet.length_toList, Std.HashSet.length_toList] at hlen

/-- `bfsGo`'s loop invariant: every frontier entry is a `domain`-confined `succs`-chain from `starts`,
and every other visited state failed `isTarget` and is closed under one more `domain`-confined step. -/
private def BfsFrontierValid (domain : Std.HashSet State) (succs : State → Array State)
    (starts : List State) (isTarget : State → Bool) (visited : Std.HashSet State)
    (frontier : List (State × List State)) : Prop :=
  (∀ q ∈ frontier, visited.contains q.1 ∧ ValidChain domain succs starts q.2.reverse q.1) ∧
  (∀ x, visited.contains x → x ∈ frontier.map Prod.fst ∨
    (isTarget x = false ∧ ∀ y, y ∈ succs x → domain.contains y → visited.contains y))

/-- The BFS level-drain loop: check the current frontier for `isTarget`, otherwise expand one more level. -/
private def bfsGo (domain : Std.HashSet State) (succs : State → Array State)
    (isTarget : State → Bool) :
    (visited : Std.HashSet State) → (∀ x, visited.contains x → domain.contains x) →
      List (State × List State) → Option (List State)
  | visited, hvd, frontier =>
    match frontier.find? (fun p => isTarget p.1) with
    | some (_, revPath) => some revPath.reverse
    | none =>
      match h : bfsExpandLevel domain succs visited frontier with
      | (_, []) => none
      | (visited', hd :: tl) =>
        have heq : (bfsExpandLevel domain succs visited frontier).1 = visited' := by rw [h]
        have heq2 : (bfsExpandLevel domain succs visited frontier).2 = hd :: tl := by rw [h]
        have hvd' : ∀ x, visited'.contains x → domain.contains x := by
          rw [← heq]; exact bfsExpandLevel_subset_domain domain succs visited frontier hvd
        have hgrow : visited.size < visited'.size := by
          have hsz := bfsExpandLevel_size_eq domain succs visited frontier
          rw [heq, heq2, List.length_cons] at hsz
          omega
        have hle : visited'.size ≤ domain.size := size_le_of_confined domain visited' hvd'
        bfsGo domain succs isTarget visited' hvd' (hd :: tl)
termination_by visited _ _ => domain.size - visited.size
decreasing_by omega

private theorem bfsGo_found_eq (domain : Std.HashSet State) (succs : State → Array State)
    (isTarget : State → Bool) (visited : Std.HashSet State)
    (hvd : ∀ x, visited.contains x → domain.contains x) (frontier : List (State × List State))
    (fst : State) (revPath : List State)
    (hfound : frontier.find? (fun p => isTarget p.1) = some (fst, revPath)) :
    bfsGo domain succs isTarget visited hvd frontier = some revPath.reverse := by
  conv => lhs; unfold bfsGo
  rw [hfound]

private theorem bfsGo_expand_empty_eq (domain : Std.HashSet State) (succs : State → Array State)
    (isTarget : State → Bool) (visited : Std.HashSet State)
    (hvd : ∀ x, visited.contains x → domain.contains x) (frontier : List (State × List State))
    (hfound : frontier.find? (fun p => isTarget p.1) = none) (fst : Std.HashSet State)
    (hexpand : bfsExpandLevel domain succs visited frontier = (fst, [])) :
    bfsGo domain succs isTarget visited hvd frontier = none := by
  unfold bfsGo
  split <;> (try split) <;> simp_all

private theorem bfsGo_expand_cons_eq (domain : Std.HashSet State) (succs : State → Array State)
    (isTarget : State → Bool) (visited : Std.HashSet State)
    (hvd : ∀ x, visited.contains x → domain.contains x) (frontier : List (State × List State))
    (hfound : frontier.find? (fun p => isTarget p.1) = none) (visited' : Std.HashSet State)
    (hd : State × List State) (tl : List (State × List State))
    (hexpand : bfsExpandLevel domain succs visited frontier = (visited', hd :: tl))
    (hvd' : ∀ x, visited'.contains x → domain.contains x) :
    bfsGo domain succs isTarget visited hvd frontier = bfsGo domain succs isTarget visited' hvd' (hd :: tl) := by
  conv => lhs; unfold bfsGo
  split <;> (try split) <;> simp_all

private theorem bfsGo_spec (domain : Std.HashSet State) (succs : State → Array State)
    (starts : List State) (isTarget : State → Bool) :
    ∀ (visited : Std.HashSet State) (hvd : ∀ x, visited.contains x → domain.contains x)
      (frontier : List (State × List State)),
    BfsFrontierValid domain succs starts isTarget visited frontier →
    (∀ path, bfsGo domain succs isTarget visited hvd frontier = some path →
      ∃ hne : path ≠ [], path.head hne ∈ starts ∧ isTarget (path.getLast hne) = true ∧
        (∀ x ∈ path, domain.contains x) ∧ ∀ i, (hi : i + 1 < path.length) → path[i+1] ∈ succs path[i]) ∧
    (bfsGo domain succs isTarget visited hvd frontier = none →
      ∃ V : Std.HashSet State, (∀ x, visited.contains x → V.contains x) ∧
        (∀ x, V.contains x → isTarget x = false) ∧
        (∀ x y, V.contains x → y ∈ succs x → domain.contains y → V.contains y))
  | visited, hvd, frontier, hinv =>
    match hfound : frontier.find? (fun p => isTarget p.1) with
    | some (fst, revPath) => by
      obtain ⟨hfrontier, _⟩ := hinv
      have heq := bfsGo_found_eq domain succs isTarget visited hvd frontier fst revPath hfound
      refine ⟨fun path hpath => ?_, fun hnone => ?_⟩
      · rw [heq] at hpath
        have hpe : revPath.reverse = path := by
          rw [Option.some.injEq] at hpath; exact hpath
        subst hpe
        have hmem : (fst, revPath) ∈ frontier := List.mem_of_find?_eq_some hfound
        have htarget : isTarget fst = true := by
          have := List.find?_some hfound
          simpa using this
        obtain ⟨hne, hhead, hlast, hconf, hchain⟩ := (hfrontier (fst, revPath) hmem).2
        exact ⟨hne, hhead, by rw [hlast]; exact htarget, hconf, hchain⟩
      · rw [heq] at hnone; exact absurd hnone (by simp)
    | none =>
      match hexpand : bfsExpandLevel domain succs visited frontier with
      | (fst, []) => by
        obtain ⟨hfrontier, hclosed⟩ := hinv
        have heq := bfsGo_expand_empty_eq domain succs isTarget visited hvd frontier hfound fst hexpand
        have hnilv := bfsExpandLevel_kept_nil_visited_eq domain succs visited frontier (by rw [hexpand])
        refine ⟨fun path hpath => ?_, fun _ => ?_⟩
        · rw [heq] at hpath; exact absurd hpath (by simp)
        · refine ⟨visited, fun x hx => hx, fun x hx => ?_, fun x y hx hy hydom => ?_⟩
          · rcases hclosed x hx with hxf | ⟨hxfalse, _⟩
            · obtain ⟨q, hq, hqx⟩ := List.mem_map.mp hxf
              have hqfalse := List.find?_eq_none.mp hfound q hq
              rw [hqx] at hqfalse; simpa using hqfalse
            · exact hxfalse
          · rcases hclosed x hx with hxf | ⟨_, hxclosed⟩
            · obtain ⟨q, hq, hqx⟩ := List.mem_map.mp hxf
              have h1 := bfsExpandLevel_closes_frontier domain succs visited frontier q hq y (hqx ▸ hy) hydom
              rw [hexpand] at h1
              exact hnilv y (by rw [hexpand]; exact h1)
            · have hy' := hxclosed y hy hydom
              have hsub := bfsExpandLevel_visited_subset domain succs visited frontier y hy'
              rw [hexpand] at hsub
              exact hnilv y (by rw [hexpand]; exact hsub)
      | (visited', hd :: tl) => by
        have hvd' : ∀ x, visited'.contains x → domain.contains x := by
          have h := bfsExpandLevel_subset_domain domain succs visited frontier hvd
          intro x hx; apply h; rw [hexpand]; exact hx
        have hgrow : visited.size < visited'.size := by
          have hsz := bfsExpandLevel_size_eq domain succs visited frontier
          rw [hexpand] at hsz
          simp only [List.length_cons] at hsz
          omega
        have hle : visited'.size ≤ domain.size := size_le_of_confined domain visited' hvd'
        obtain ⟨hfrontier, hclosed⟩ := hinv
        have hinv' : BfsFrontierValid domain succs starts isTarget visited' (hd :: tl) := by
          constructor
          · intro q hq
            have hq' : q ∈ (bfsExpandLevel domain succs visited frontier).2 := by rw [hexpand]; exact hq
            refine ⟨?_, ?_⟩
            · have h := bfsExpandLevel_kept_subset_visited domain succs visited frontier q hq'
              rw [hexpand] at h; exact h
            · exact bfsExpandLevel_kept_valid domain succs starts visited frontier
                (fun r hr => (hfrontier r hr).2) q hq'
          · intro x hx
            have hx' : (bfsExpandLevel domain succs visited frontier).1.contains x := by rw [hexpand]; exact hx
            rcases bfsExpandLevel_visited_eq_or_kept domain succs visited frontier x hx' with hxold | ⟨p, hp, hpx⟩
            · rcases hclosed x hxold with hxf | ⟨hxfalse, hxclosed⟩
              · obtain ⟨q, hq, hqx⟩ := List.mem_map.mp hxf
                have hqfalse := List.find?_eq_none.mp hfound q hq
                rw [hqx] at hqfalse
                refine Or.inr ⟨by simpa using hqfalse, ?_⟩
                intro y hy hydom
                have h := bfsExpandLevel_closes_frontier domain succs visited frontier q hq y (hqx ▸ hy) hydom
                rw [hexpand] at h; exact h
              · refine Or.inr ⟨hxfalse, ?_⟩
                intro y hy hydom
                have h := hxclosed y hy hydom
                have hsub := bfsExpandLevel_visited_subset domain succs visited frontier y h
                rw [hexpand] at hsub; exact hsub
            · refine Or.inl ?_
              rw [hexpand] at hp
              exact List.mem_map.mpr ⟨p, hp, hpx⟩
        have ih := bfsGo_spec domain succs starts isTarget visited' hvd' (hd :: tl) hinv'
        rw [bfsGo_expand_cons_eq domain succs isTarget visited hvd frontier hfound visited' hd tl hexpand hvd']
        refine ⟨ih.1, fun hnone => ?_⟩
        obtain ⟨V, hV1, hV2, hV3⟩ := ih.2 hnone
        have hvv' : ∀ x, visited.contains x → visited'.contains x := by
          have h := bfsExpandLevel_visited_subset domain succs visited frontier
          intro x hx; rw [hexpand] at h; exact h x hx
        exact ⟨V, fun x hx => hV1 x (hvv' x hx), hV2, hV3⟩
termination_by visited _ _ _ => domain.size - visited.size
decreasing_by omega

/-- BFS from `starts`, following `succs`, confined to `domain`. Returns a path, both ends included, to some `isTarget`
state reachable from `starts` within `domain`. -/
def bfsFindPath (domain : Std.HashSet State) (succs : State → Array State) (starts : List State)
    (isTarget : State → Bool) : Option (List State) :=
  let starts' := starts.filter domain.contains
  bfsGo domain succs isTarget (Std.HashSet.ofList starts')
    (fun _ hx =>
      (List.mem_filter.mp (List.contains_iff_mem.mp
        ((Std.HashSet.mem_ofList (l := starts')).mp
          (Std.HashSet.mem_iff_contains.mpr hx)))).2)
    (starts'.map fun s => (s, [s]))

private theorem bfsFindPath_frontier_valid (domain : Std.HashSet State) (succs : State → Array State)
    (starts : List State) (isTarget : State → Bool) :
    BfsFrontierValid domain succs starts isTarget (Std.HashSet.ofList (starts.filter domain.contains))
      ((starts.filter domain.contains).map fun s => (s, [s])) := by
  set starts' := starts.filter domain.contains with hstarts'
  constructor
  · intro q hq
    obtain ⟨s, hsmem, hsq⟩ := List.mem_map.mp hq
    have hsstarts : s ∈ starts := (List.mem_filter.mp hsmem).1
    have hsdom : domain.contains s := (List.mem_filter.mp hsmem).2
    subst hsq
    refine ⟨?_, ValidChain.singleton hsstarts hsdom⟩
    exact (Std.HashSet.mem_iff_contains).mp
      ((Std.HashSet.mem_ofList (l := starts')).mpr (List.contains_iff_mem.mpr hsmem))
  · intro x hx
    left
    have hxmem : x ∈ starts' :=
      List.contains_iff_mem.mp ((Std.HashSet.mem_ofList (l := starts')).mp (Std.HashSet.mem_iff_contains.mpr hx))
    simpa using hxmem

/-- `bfsFindPath`'s soundness: a `some` result is a `domain`-confined `succs`-chain from `starts` to an `isTarget`-satisfying state. -/
theorem bfsFindPath_sound (domain : Std.HashSet State) (succs : State → Array State)
    (starts : List State) (isTarget : State → Bool) :
    ∀ path, bfsFindPath domain succs starts isTarget = some path →
      ∃ hne : path ≠ [], path.head hne ∈ starts ∧ isTarget (path.getLast hne) = true ∧
        (∀ x ∈ path, domain.contains x) ∧ ∀ i, (hi : i + 1 < path.length) → path[i+1] ∈ succs path[i] :=
  (bfsGo_spec domain succs starts isTarget _ _ _ (bfsFindPath_frontier_valid domain succs starts isTarget)).1

/-- If an `isTarget` state is reachable from `starts` along a `domain`-confined path, `bfsFindPath` finds one. -/
theorem bfsFindPath_complete (domain : Std.HashSet State) (succs : State → Array State)
    (starts : List State) (isTarget : State → Bool)
    (hex : ∃ s0 ∈ starts, domain.contains s0 ∧ ∃ t, domain.contains t ∧ isTarget t = true ∧
      (s0 = t ∨ PathTo succs (fun x => ¬ domain.contains x) s0 t)) :
    ∃ path, bfsFindPath domain succs starts isTarget = some path := by
  obtain ⟨s0, hs0starts, hs0dom, t, htdom, httarget, hreach⟩ := hex
  cases h : bfsFindPath domain succs starts isTarget with
  | some path => exact ⟨path, rfl⟩
  | none =>
    exfalso
    obtain ⟨V, hVsup, hVtarget, hVclosed⟩ :=
      (bfsGo_spec domain succs starts isTarget _ _ _ (bfsFindPath_frontier_valid domain succs starts isTarget)).2 h
    have hs0mem : s0 ∈ starts.filter domain.contains := List.mem_filter.mpr ⟨hs0starts, hs0dom⟩
    have hs0V : V.contains s0 := hVsup s0 ((Std.HashSet.mem_iff_contains).mp
      ((Std.HashSet.mem_ofList (l := starts.filter domain.contains)).mpr
        (List.contains_iff_mem.mpr hs0mem)))
    have htV : V.contains t := by
      rcases hreach with rfl | hpath
      · exact hs0V
      · exact hpath.mem_of_closed hVclosed hs0V htdom
    have := hVtarget t htV
    rw [httarget] at this
    exact absurd this (by simp)

/-- Over a domain holding every reachable state, the BFS from the initial states finds a stem to any reachable target. -/
theorem bfsFindPath_stem {domain : Std.HashSet State} {succs : State → Array State} {initialStates : List State}
    {anchor : State} (hdom : ∀ s, Reachable initialStates succs s → s ∈ domain)
    (ha : Reachable initialStates succs anchor) :
    ∃ path, bfsFindPath domain succs initialStates (· == anchor) = some path ∧
      ∃ hs : path ≠ [], path.head hs ∈ initialStates ∧
        (∀ i, (hi : i + 1 < path.length) → path[i + 1] ∈ succs (path[i])) ∧ path.getLast hs = anchor := by
  obtain ⟨s0, hs0, hp⟩ := ha.exists_pathTo
  obtain ⟨path, hpath⟩ := bfsFindPath_complete domain succs initialStates (· == anchor)
    ⟨s0, hs0, Std.HashSet.mem_iff_contains.mp (hdom s0 (.base hs0)), anchor,
      Std.HashSet.mem_iff_contains.mp (hdom anchor ha), by simp,
      hp.imp id fun h => h.weaken fun x hx hr => hx (Std.HashSet.mem_iff_contains.mp (hdom x hr))⟩
  obtain ⟨hne, hhead, htarget, -, hchain⟩ := bfsFindPath_sound domain succs initialStates (· == anchor) path hpath
  exact ⟨path, hpath, hne, hhead, hchain, by simpa using htarget⟩

end Bfs

/-! ## Adaptive edge search and cycle stitching -/

/-- Any edge inside `scc`. -/
def findAnyEdge (succs : State → Array State) (scc : Std.HashSet State) :
    Option (State × State) :=
  scc.toList.findSome? fun a =>
    ((succs a).toList.find? fun b => scc.contains b).map fun b => (a, b)

/-- A returned edge is real and `scc`-confined on both ends. -/
theorem findAnyEdge_sound [LawfulBEq State] (succs : State → Array State) (scc : Std.HashSet State)
    (a b : State) (h : findAnyEdge succs scc = some (a, b)) :
    scc.contains a ∧ scc.contains b ∧ b ∈ succs a := by
  obtain ⟨a', ha', hmap⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨b', hfind, heq⟩ := Option.map_eq_some_iff.mp hmap
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  have hp := List.find?_some hfind
  refine ⟨(Std.HashSet.mem_iff_contains).mp ((Std.HashSet.mem_toList (m := scc)).mp ha'), hp, ?_⟩
  simpa using List.mem_of_find?_eq_some hfind

/-- If some real edge inside `scc` exists at all, `findAnyEdge` finds one. -/
theorem findAnyEdge_complete [LawfulBEq State] (succs : State → Array State) (scc : Std.HashSet State)
    (h : ∃ a ∈ scc, ∃ b ∈ scc, b ∈ succs a) : ∃ a b, findAnyEdge succs scc = some (a, b) := by
  obtain ⟨a, ha, b, hb, hedge⟩ := h
  have hshow : (scc.toList.findSome? fun a =>
      ((succs a).toList.find? fun b => scc.contains b).map fun b => (a, b)).isSome := by
    rw [List.findSome?_isSome_iff]
    refine ⟨a, (Std.HashSet.mem_toList (m := scc)).mpr ha, ?_⟩
    rw [Option.isSome_map, List.find?_isSome]
    exact ⟨b, by simpa using hedge, (Std.HashSet.mem_iff_contains).mp hb⟩
  obtain ⟨⟨a', b'⟩, heq⟩ := Option.isSome_iff_exists.mp hshow
  exact ⟨a', b', heq⟩

/-- One of `a`'s `scc`-confined successors carrying a mark still in `remaining`, if any. -/
def pickMarkedNext (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (scc : Std.HashSet State) (remaining : Std.HashSet Nat) (a : State) : Option State :=
  (succs a).toList.find? fun b => scc.contains b && (edgeMarks a b).toList.any remaining.contains

/-- A returned successor is real, `scc`-confined, and carries a mark still in `remaining`. -/
theorem pickMarkedNext_sound (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (scc : Std.HashSet State)
    (remaining : Std.HashSet Nat) (a b : State)
    (h : pickMarkedNext succs edgeMarks scc remaining a = some b) :
    b ∈ succs a ∧ scc.contains b ∧ ∃ m, remaining.contains m ∧ (edgeMarks a b).contains m := by
  have hmem := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true] at hp
  obtain ⟨m, hm, hmark⟩ := List.any_eq_true.mp hp.2
  exact ⟨by simpa using hmem, hp.1, m, hmark,
    (Std.HashSet.mem_iff_contains).mp ((Std.HashSet.mem_toList (m := edgeMarks a b)).mp hm)⟩

/-- If some real `scc`-confined successor of `a` carries a mark still in `remaining`, `pickMarkedNext` finds one. -/
theorem pickMarkedNext_complete (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (scc : Std.HashSet State)
    (remaining : Std.HashSet Nat) (a : State)
    (h : ∃ b, scc.contains b ∧ b ∈ succs a ∧ ∃ m, remaining.contains m ∧ (edgeMarks a b).contains m) :
    ∃ b, pickMarkedNext succs edgeMarks scc remaining a = some b := by
  obtain ⟨b, hb, hedge, m, hm, hmark⟩ := h
  rw [← Option.isSome_iff_exists]
  unfold pickMarkedNext
  rw [List.find?_isSome]
  refine ⟨b, by simpa using hedge, ?_⟩
  simp only [Bool.and_eq_true, List.any_eq_true]
  exact ⟨hb, m, (Std.HashSet.mem_toList (m := edgeMarks a b)).mpr
    ((Std.HashSet.mem_iff_contains).mpr hmark), hm⟩

/-- A `succs`-path from `src` to `tgt` inclusive, confined to `domain`, or the fallback `[src]` if there is none. -/
def connector [LawfulBEq State] [LawfulHashable State] (domain : Std.HashSet State)
    (succs : State → Array State) (src tgt : State) : List State :=
  (bfsFindPath domain succs [src] (· == tgt)).getD [src]

/-- Whenever `tgt` is reachable from `src` via a `domain`-confined `succs`-path, `connector` returns a genuine one. -/
theorem connector_valid [LawfulBEq State] [LawfulHashable State] (domain : Std.HashSet State)
    (succs : State → Array State) (src tgt : State) (hsrc : domain.contains src)
    (htgt : domain.contains tgt)
    (hreach : src = tgt ∨ PathTo succs (fun x => ¬ domain.contains x) src tgt) :
    ValidChain domain succs [src] (connector domain succs src tgt) tgt := by
  unfold connector
  obtain ⟨path, hpath⟩ := bfsFindPath_complete domain succs [src] (· == tgt)
    ⟨src, List.mem_singleton_self src, hsrc, tgt, htgt, by simp, hreach⟩
  rw [hpath, Option.getD_some]
  obtain ⟨hne, hhead, hlast, hconf, hchain⟩ := bfsFindPath_sound domain succs [src] (· == tgt) path hpath
  exact ⟨hne, hhead, beq_iff_eq.mp hlast, hconf, hchain⟩

/-- `connector` never returns the empty list. -/
theorem connector_ne_nil [LawfulBEq State] [LawfulHashable State] (domain : Std.HashSet State)
    (succs : State → Array State) (src tgt : State) : connector domain succs src tgt ≠ [] := by
  unfold connector
  cases h : bfsFindPath domain succs [src] (· == tgt) with
  | none => simp
  | some path =>
    obtain ⟨hne, _⟩ := bfsFindPath_sound domain succs [src] (· == tgt) path h
    simpa using hne

private theorem size_filter_not_contains_lt (s t : Std.HashSet Nat)
    (h : ∃ x, s.contains x ∧ t.contains x) :
    (s.filter fun x => !t.contains x).size < s.size := by
  obtain ⟨x, hsx, htx⟩ := h
  have hle : (s.filter fun x => !t.contains x).size ≤ s.size := Std.HashSet.size_filter_le_size
  have hne : (s.filter fun x => !t.contains x).size ≠ s.size := fun heq => by
    rw [Std.HashSet.size_filter_eq_size_iff] at heq
    have hk := heq x ((Std.HashSet.mem_iff_contains).mpr hsx)
    rw [Std.HashSet.get_eq] at hk
    simp [htx] at hk
  omega

/-- Adaptively chain BFS's from `cur` back to `anchor`: each round searches `scc` for the nearest state with
an outgoing edge covering a mark still in `remaining`, follows it, and drops its marks, until none are left. -/
def buildCycleFrom [LawfulBEq State] [LawfulHashable State] (scc : Std.HashSet State)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat) (anchor : State) :
    State → Std.HashSet Nat → List State
  | cur, remaining =>
    if _hrem : remaining.isEmpty = true then
      connector scc succs cur anchor
    else
      match bfsFindPath scc succs [cur]
          fun a => (pickMarkedNext succs edgeMarks scc remaining a).isSome with
      | none => []
      | some path =>
        match path.getLast? with
        | none => []
        | some a =>
          match _h : pickMarkedNext succs edgeMarks scc remaining a with
          | none => []
          | some b =>
            path ++ buildCycleFrom scc succs edgeMarks anchor b
              (remaining.filter fun x => !(edgeMarks a b).contains x)
termination_by _cur remaining => remaining.size
decreasing_by
  obtain ⟨_, _, m, hm1, hm2⟩ := pickMarkedNext_sound succs edgeMarks scc remaining a b _h
  have := size_filter_not_contains_lt remaining (edgeMarks a b) ⟨m, hm1, hm2⟩
  omega

/-- An accepting cycle anchored at `anchor`, covering every mark `< numMarks`, through a `findAnyEdge` edge when
`numMarks = 0` and chained by `buildCycleFrom` otherwise. It is not minimized. -/
def stitchCycleAt [LawfulBEq State] [LawfulHashable State] (scc : Std.HashSet State)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat) (numMarks : Nat)
    (anchor : State) : List State :=
  if numMarks = 0 then
    match findAnyEdge succs scc with
    | none => []
    | some (a, b) => (connector scc succs anchor a ++ connector scc succs b anchor).dropLast
  else
    (buildCycleFrom scc succs edgeMarks anchor anchor (Std.HashSet.ofList (List.range numMarks))).dropLast

omit [BEq State] [Hashable State] in
private theorem chain_covers_prepend {edgeMarks : State → State → Std.HashSet Nat}
    (prefix' suffix : List State) {m : Nat}
    (h : ∃ (i : Nat) (hi : i + 1 < suffix.length), m ∈ edgeMarks (suffix[i]) (suffix[i + 1])) :
    ∃ (i : Nat) (hi : i + 1 < (prefix' ++ suffix).length),
      m ∈ edgeMarks ((prefix' ++ suffix)[i]) ((prefix' ++ suffix)[i + 1]) := by
  obtain ⟨i, hi, hm⟩ := h
  have hilt : i < suffix.length := by omega
  have hi1lt : i + 1 < suffix.length := hi
  have e1 := List.getElem_append_right' prefix' hilt
  have e2 := List.getElem_append_right' prefix' hi1lt
  refine ⟨i + prefix'.length, by simp only [List.length_append]; omega, ?_⟩
  simp only [show i + prefix'.length + 1 = (i + 1) + prefix'.length from by omega, ← e1, ← e2]
  exact hm

private theorem buildCycleFrom_empty_eq [LawfulBEq State] [LawfulHashable State]
    (scc : Std.HashSet State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (anchor cur : State) (remaining : Std.HashSet Nat)
    (hrem : remaining.isEmpty = true) :
    buildCycleFrom scc succs edgeMarks anchor cur remaining = connector scc succs cur anchor := by
  conv => lhs; unfold buildCycleFrom
  rw [dif_pos hrem]

private theorem buildCycleFrom_next_eq [LawfulBEq State] [LawfulHashable State]
    (scc : Std.HashSet State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (anchor cur : State) (remaining : Std.HashSet Nat)
    (hrem : remaining.isEmpty = false) (path : List State)
    (hpath : bfsFindPath scc succs [cur]
      (fun a => (pickMarkedNext succs edgeMarks scc remaining a).isSome) = some path)
    (a : State) (hlast : path.getLast? = some a) (b : State)
    (hpick : pickMarkedNext succs edgeMarks scc remaining a = some b) :
    buildCycleFrom scc succs edgeMarks anchor cur remaining =
      path ++ buildCycleFrom scc succs edgeMarks anchor b
        (remaining.filter fun x => !(edgeMarks a b).contains x) := by
  conv => lhs; unfold buildCycleFrom
  rw [dif_neg (by simp [hrem] : ¬ remaining.isEmpty = true), hpath]
  dsimp only
  rw [hlast]
  dsimp only
  rw [hpick]

private theorem buildCycleFrom_valid [LawfulBEq State] [LawfulHashable State]
    (scc : Std.HashSet State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (anchor : State)
    (hconn : ∀ s, scc.contains s → ∀ t, scc.contains t →
      s = t ∨ PathTo succs (fun x => ¬ scc.contains x) s t)
    (hanchor : scc.contains anchor) :
    ∀ (cur : State) (remaining : Std.HashSet Nat), scc.contains cur →
      (∀ m, remaining.contains m →
        ∃ s, scc.contains s ∧ ∃ t, scc.contains t ∧ t ∈ succs s ∧ m ∈ edgeMarks s t) →
      ∀ result, buildCycleFrom scc succs edgeMarks anchor cur remaining = result →
      ∃ hne : result ≠ [], result.head hne = cur ∧ result.getLast hne = anchor ∧
        (∀ x ∈ result, scc.contains x) ∧
        (∀ i, (hi : i + 1 < result.length) → result[i + 1] ∈ succs result[i]) ∧
        ∀ m, remaining.contains m → ∃ (i : Nat) (hi : i + 1 < result.length),
          m ∈ edgeMarks (result[i]) (result[i + 1])
  | cur, remaining, hcur, hcov, result, hresult =>
    match hrem : remaining.isEmpty with
    | true => by
      have heq : connector scc succs cur anchor = result :=
        (buildCycleFrom_empty_eq scc succs edgeMarks anchor cur remaining hrem).symm.trans hresult
      subst heq
      obtain ⟨hne, hhead, hlast, hconf, hchain⟩ :=
        connector_valid scc succs cur anchor hcur hanchor (hconn cur hcur anchor hanchor)
      exact ⟨hne, List.mem_singleton.mp hhead, hlast, hconf, hchain, fun m hm => by
        have := Std.HashSet.isEmpty_iff_forall_contains.mp hrem m
        simp [this] at hm⟩
    | false => by
      obtain ⟨m0, hm0⟩ := Std.HashSet.isEmpty_eq_false_iff_exists_contains_eq_true.mp hrem
      obtain ⟨s, hs, t, ht, hedge, hmark⟩ := hcov m0 hm0
      have htarget : (pickMarkedNext succs edgeMarks scc remaining s).isSome := by
        obtain ⟨b, hb⟩ := pickMarkedNext_complete succs edgeMarks scc remaining s
          ⟨t, ht, hedge, m0, hm0, (Std.HashSet.mem_iff_contains).mp hmark⟩
        simp [hb]
      obtain ⟨path, hpath⟩ := bfsFindPath_complete scc succs [cur]
        (fun a => (pickMarkedNext succs edgeMarks scc remaining a).isSome)
        ⟨cur, List.mem_singleton_self cur, hcur, s, hs, htarget, hconn cur hcur s hs⟩
      obtain ⟨hpne, hphead, hptarget, hpconf, hpchain⟩ :=
        bfsFindPath_sound scc succs [cur] (fun a => (pickMarkedNext succs edgeMarks scc remaining a).isSome)
          path hpath
      have ha : path.getLast? = some (path.getLast hpne) := List.getLast?_eq_some_getLast hpne
      set a := path.getLast hpne with hadef
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hptarget
      obtain ⟨hedgeab, hbdom, m1, hm1rem, hm1mark⟩ := pickMarkedNext_sound succs edgeMarks scc remaining a b hb
      have hshrink := size_filter_not_contains_lt remaining (edgeMarks a b) ⟨m1, hm1rem, hm1mark⟩
      have hcov' : ∀ m, (remaining.filter fun x => !(edgeMarks a b).contains x).contains m →
          ∃ s, scc.contains s ∧ ∃ t, scc.contains t ∧ t ∈ succs s ∧ m ∈ edgeMarks s t :=
        fun m hm => hcov m (Std.HashSet.contains_of_contains_filter hm)
      obtain ⟨hrne, hrhead, hrlast, hrconf, hrchain, hrcov⟩ :=
        buildCycleFrom_valid scc succs edgeMarks anchor hconn hanchor b
          (remaining.filter fun x => !(edgeMarks a b).contains x) hbdom hcov'
          (buildCycleFrom scc succs edgeMarks anchor b (remaining.filter fun x => !(edgeMarks a b).contains x)) rfl
      have heq : path ++ buildCycleFrom scc succs edgeMarks anchor b
          (remaining.filter fun x => !(edgeMarks a b).contains x) = result :=
        (buildCycleFrom_next_eq scc succs edgeMarks anchor cur remaining (by simp [hrem]) path hpath
          a ha b hb).symm.trans hresult
      subst heq
      have hheadedge : (buildCycleFrom scc succs edgeMarks anchor b
          (remaining.filter fun x => !(edgeMarks a b).contains x)).head hrne ∈ succs a := by
        rw [hrhead]; exact hedgeab
      have hcombchain := chain_append path _ hpchain hrchain hpne hrne hheadedge
      have hcombne : path ++ buildCycleFrom scc succs edgeMarks anchor b
          (remaining.filter fun x => !(edgeMarks a b).contains x) ≠ [] := by simp [hpne]
      have hplen : 0 < path.length := List.length_pos_iff.mpr hpne
      refine ⟨hcombne, ?_, ?_, ?_, hcombchain, ?_⟩
      · rw [List.head_append_of_ne_nil hpne]; exact List.mem_singleton.mp hphead
      · rw [List.getLast_append_of_ne_nil _ hrne]; exact hrlast
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hpconf x hx
        · exact hrconf x hx
      · intro m hm
        by_cases hmab : (edgeMarks a b).contains m
        · have hlen : (path ++ buildCycleFrom scc succs edgeMarks anchor b
              (remaining.filter fun x => !(edgeMarks a b).contains x)).length =
              path.length + (buildCycleFrom scc succs edgeMarks anchor b
                (remaining.filter fun x => !(edgeMarks a b).contains x)).length := List.length_append
          have hrlen : 0 < (buildCycleFrom scc succs edgeMarks anchor b
              (remaining.filter fun x => !(edgeMarks a b).contains x)).length := List.length_pos_iff.mpr hrne
          have hsubadd : path.length - 1 + 1 = path.length := Nat.sub_add_cancel hplen
          have hbound0 : path.length - 1 + 1 < (path ++ buildCycleFrom scc succs edgeMarks anchor b
              (remaining.filter fun x => !(edgeMarks a b).contains x)).length := by omega
          have hbound1 : path.length - 1 < (path ++ buildCycleFrom scc succs edgeMarks anchor b
              (remaining.filter fun x => !(edgeMarks a b).contains x)).length := by omega
          refine ⟨path.length - 1, hbound0, ?_⟩
          have e0 : (path ++ buildCycleFrom scc succs edgeMarks anchor b
              (remaining.filter fun x => !(edgeMarks a b).contains x))[path.length - 1]'hbound1 = a := by
            rw [List.getElem_append_left (by omega), ← List.getLast_eq_getElem]
          have hbound0' : path.length ≤ path.length - 1 + 1 := by omega
          have e1 : (path ++ buildCycleFrom scc succs edgeMarks anchor b
              (remaining.filter fun x => !(edgeMarks a b).contains x))[path.length - 1 + 1]'hbound0 = b := by
            have hstep : (path ++ buildCycleFrom scc succs edgeMarks anchor b
                (remaining.filter fun x => !(edgeMarks a b).contains x))[path.length - 1 + 1]'hbound0 =
                (buildCycleFrom scc succs edgeMarks anchor b
                  (remaining.filter fun x => !(edgeMarks a b).contains x))[path.length - 1 + 1 - path.length]'(by
                    omega) :=
              List.getElem_append_right hbound0'
            have hstep2 : (buildCycleFrom scc succs edgeMarks anchor b
                (remaining.filter fun x => !(edgeMarks a b).contains x))[path.length - 1 + 1 - path.length]'(by omega) =
                (buildCycleFrom scc succs edgeMarks anchor b
                (remaining.filter fun x => !(edgeMarks a b).contains x))[0]'hrlen := by
              congr 1
              omega
            rw [hstep, hstep2]
            simpa using (List.head_eq_getElem hrne).symm.trans hrhead
          rw [e0, e1]
          exact (Std.HashSet.mem_iff_contains).mp hmab
        · have hmfilt : (remaining.filter fun x => !(edgeMarks a b).contains x).contains m := by
            have hmmem : m ∈ remaining.filter fun x => !(edgeMarks a b).contains x :=
              Std.HashSet.mem_filter.mpr ⟨(Std.HashSet.mem_iff_contains).mpr hm, by
                rw [Std.HashSet.get_eq]; simpa using hmab⟩
            exact (Std.HashSet.mem_iff_contains).mp hmmem
          obtain ⟨i, hi, hcovi⟩ := hrcov m hmfilt
          exact chain_covers_prepend path _ ⟨i, hi, hcovi⟩
termination_by cur remaining _ _ _ _ => remaining.size
decreasing_by exact hshrink

private theorem stitchCycleAt_zero_eq [LawfulBEq State] [LawfulHashable State]
    (scc : Std.HashSet State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (anchor a b : State)
    (hfind : findAnyEdge succs scc = some (a, b)) :
    stitchCycleAt scc succs edgeMarks 0 anchor =
      (connector scc succs anchor a ++ connector scc succs b anchor).dropLast := by
  conv => lhs; unfold stitchCycleAt
  rw [if_pos rfl, hfind]

private theorem stitchCycleAt_pos_eq [LawfulBEq State] [LawfulHashable State]
    (scc : Std.HashSet State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (numMarks : Nat) (anchor : State)
    (hnm : numMarks ≠ 0) :
    stitchCycleAt scc succs edgeMarks numMarks anchor =
      (buildCycleFrom scc succs edgeMarks anchor anchor (Std.HashSet.ofList (List.range numMarks))).dropLast := by
  conv => lhs; unfold stitchCycleAt
  rw [if_neg hnm]

/-- `stitchCycleAt` is a `scc`-confined cycle anchored at `anchor`, covering every mark `< numMarks`,
indexed modularly since the covering edge may be the wraparound one. -/
theorem stitchCycleAt_valid [LawfulBEq State] [LawfulHashable State] (scc : Std.HashSet State)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat) (numMarks : Nat)
    (anchor : State) (hmarks : AcceptingMarks succs edgeMarks numMarks scc)
    (hconn : ∀ s, scc.contains s → ∀ t, scc.contains t →
      s = t ∨ PathTo succs (fun x => ¬ scc.contains x) s t)
    (hanchor : scc.contains anchor) (result : List State)
    (hresult : stitchCycleAt scc succs edgeMarks numMarks anchor = result) :
    ∃ hne : result ≠ [], result.head hne = anchor ∧
      (∀ x ∈ result, scc.contains x) ∧
      (∀ i, (hi : i + 1 < result.length) → result[i + 1] ∈ succs result[i]) ∧
      result.head hne ∈ succs (result.getLast hne) ∧
      ∀ m, m < numMarks → ∃ (i : Nat) (hi : i < result.length),
        m ∈ edgeMarks (result[i]) (result[(i + 1) % result.length]'(Nat.mod_lt _ (List.length_pos_iff.mpr hne))) := by
  rcases Nat.eq_zero_or_pos numMarks with hnm | hnm
  · obtain ⟨s0, hs0, t0, ht0, hedge0⟩ := hmarks.1
    obtain ⟨a, b, hfind⟩ := findAnyEdge_complete succs scc
      ⟨s0, (Std.HashSet.mem_iff_contains).mp hs0, t0, (Std.HashSet.mem_iff_contains).mp ht0, hedge0⟩
    obtain ⟨ha, hb, hedge⟩ := findAnyEdge_sound succs scc a b hfind
    have heq : (connector scc succs anchor a ++ connector scc succs b anchor).dropLast = result := by
      rw [← hresult, hnm]; exact (stitchCycleAt_zero_eq scc succs edgeMarks anchor a b hfind).symm
    subst heq
    obtain ⟨hnea, hheada, hlasta, hconfa, hchaina⟩ :=
      connector_valid scc succs anchor a hanchor ha (hconn anchor hanchor a ha)
    obtain ⟨hneb, hheadb, hlastb, hconfb, hchainb⟩ :=
      connector_valid scc succs b anchor hb hanchor (hconn b hb anchor hanchor)
    have hheadaeq : (connector scc succs anchor a).head hnea = anchor := List.mem_singleton.mp hheada
    have hheadbeq : (connector scc succs b anchor).head hneb = b := List.mem_singleton.mp hheadb
    have hjunc : (connector scc succs b anchor).head hneb ∈ succs ((connector scc succs anchor a).getLast hnea) := by
      rw [hlasta, hheadbeq]; exact hedge
    have hcomb := chain_append (connector scc succs anchor a) (connector scc succs b anchor)
      hchaina hchainb hnea hneb hjunc
    have hcombne : connector scc succs anchor a ++ connector scc succs b anchor ≠ [] := by simp [hnea]
    have hcombhead : (connector scc succs anchor a ++ connector scc succs b anchor).head hcombne = anchor := by
      rw [List.head_append_of_ne_nil hnea]; exact hheadaeq
    have hcombgetlast : (connector scc succs anchor a ++ connector scc succs b anchor).getLast hcombne =
        anchor := by rw [List.getLast_append_of_ne_nil _ hneb]; exact hlastb
    have hplen : 0 < (connector scc succs anchor a).length := List.length_pos_iff.mpr hnea
    have hplenb : 0 < (connector scc succs b anchor).length := List.length_pos_iff.mpr hneb
    have hcomblen : (connector scc succs anchor a ++ connector scc succs b anchor).length =
        (connector scc succs anchor a).length + (connector scc succs b anchor).length := List.length_append
    have hdlen : (connector scc succs anchor a ++ connector scc succs b anchor).dropLast.length =
        (connector scc succs anchor a ++ connector scc succs b anchor).length - 1 := List.length_dropLast
    have hcycleposlen : 0 < (connector scc succs anchor a ++ connector scc succs b anchor).dropLast.length := by
      omega
    have hcyclene : (connector scc succs anchor a ++ connector scc succs b anchor).dropLast ≠ [] :=
      List.ne_nil_of_length_pos hcycleposlen
    refine ⟨hcyclene, ?_, ?_, chain_dropLast _ hcomb, ?_, fun m hm => absurd hm (by omega)⟩
    · rw [head_dropLast_eq _ hcombne hcyclene, hcombhead]
    · intro x hx
      have hxc := List.dropLast_subset _ hx
      rcases List.mem_append.mp hxc with hxa | hxb
      · exact hconfa x hxa
      · exact hconfb x hxb
    · rw [head_dropLast_eq _ hcombne hcyclene, hcombhead]
      have := chain_getLast_edge _ hcombne hcyclene hcomb
      rwa [hcombgetlast] at this
  · have hcov : ∀ m, (Std.HashSet.ofList (List.range numMarks)).contains m →
        ∃ s, scc.contains s ∧ ∃ t, scc.contains t ∧ t ∈ succs s ∧ m ∈ edgeMarks s t := by
      intro m hm
      have hmr : m ∈ List.range numMarks :=
        List.contains_iff_mem.mp ((Std.HashSet.mem_ofList).mp (Std.HashSet.mem_iff_contains.mpr hm))
      obtain ⟨s, hs, t, ht, hedge, hmark⟩ := hmarks.2 m (List.mem_range.mp hmr)
      exact ⟨s, (Std.HashSet.mem_iff_contains).mp hs, t, (Std.HashSet.mem_iff_contains).mp ht, hedge, hmark⟩
    obtain ⟨hrne, hrhead, hrlast, hrconf, hrchain, hrcov⟩ :=
      buildCycleFrom_valid scc succs edgeMarks anchor hconn hanchor anchor
        (Std.HashSet.ofList (List.range numMarks)) hanchor hcov
        (buildCycleFrom scc succs edgeMarks anchor anchor (Std.HashSet.ofList (List.range numMarks))) rfl
    have heq : (buildCycleFrom scc succs edgeMarks anchor anchor
        (Std.HashSet.ofList (List.range numMarks))).dropLast = result := by
      rw [← hresult]
      exact (stitchCycleAt_pos_eq scc succs edgeMarks numMarks anchor (by omega)).symm
    subst heq
    have hm0 : (Std.HashSet.ofList (List.range numMarks)).contains 0 :=
      (Std.HashSet.mem_iff_contains).mp
        ((Std.HashSet.mem_ofList).mpr (List.contains_iff_mem.mpr (List.mem_range.mpr hnm)))
    obtain ⟨i0, hi0, hcov0⟩ := hrcov 0 hm0
    have hplen : 0 < (buildCycleFrom scc succs edgeMarks anchor anchor
        (Std.HashSet.ofList (List.range numMarks))).length := by omega
    have hcyclene : (buildCycleFrom scc succs edgeMarks anchor anchor
        (Std.HashSet.ofList (List.range numMarks))).dropLast ≠ [] :=
      List.ne_nil_of_length_pos (by rw [List.length_dropLast]; omega)
    refine ⟨hcyclene, ?_, ?_, chain_dropLast _ hrchain, ?_, ?_⟩
    · rw [head_dropLast_eq _ hrne hcyclene, hrhead]
    · intro x hx
      exact hrconf x (List.dropLast_subset _ hx)
    · rw [head_dropLast_eq _ hrne hcyclene, hrhead]
      have := chain_getLast_edge _ hrne hcyclene hrchain
      rwa [hrlast] at this
    · intro m hm
      have hmset : (Std.HashSet.ofList (List.range numMarks)).contains m :=
        (Std.HashSet.mem_iff_contains).mp
          ((Std.HashSet.mem_ofList).mpr (List.contains_iff_mem.mpr (List.mem_range.mpr hm)))
      obtain ⟨i, hi, hcov'⟩ := hrcov m hmset
      have hloop : (buildCycleFrom scc succs edgeMarks anchor anchor
          (Std.HashSet.ofList (List.range numMarks))).getLast hrne =
          (buildCycleFrom scc succs edgeMarks anchor anchor
          (Std.HashSet.ofList (List.range numMarks))).head hrne := by rw [hrhead, hrlast]
      simpa using mark_pos_dropLast _ [] hrne hi (by simpa using hcov')
        (by simpa using hrne) (by simpa using hloop)

/-- A `stitchCycleAt` cycle in an accepting, internally connected `scc` and a stem to its anchor form a
`TAcceptingCycle`. -/
theorem stitchCycleAt_toTAcceptingCycle [LawfulBEq State] [LawfulHashable State]
    {initialStates : List State} {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat}
    {scc : Std.HashSet State} {anchor : State} {stem : List State}
    (hconnected : InternallyConnected succs scc) (hcovers : AcceptingMarks succs edgeMarks numMarks scc)
    (hanchor : anchor ∈ scc) (hstemne : stem ≠ []) (hstemhead : stem.head hstemne ∈ initialStates)
    (hstemchain : ∀ i, (hi : i + 1 < stem.length) → stem[i + 1] ∈ succs stem[i])
    (hstemlast : stem.getLast hstemne = anchor) :
    ∃ ac : TAcceptingCycle initialStates succs edgeMarks numMarks, ac.stem = stem ∧
      ac.cycle = stitchCycleAt scc (sccSuccs succs scc) edgeMarks numMarks anchor := by
  set succs' := sccSuccs succs scc with hsuccs'def
  have hcovers' : AcceptingMarks succs' edgeMarks numMarks scc := hcovers.sccSuccs
  have hconn' : ∀ s, scc.contains s → ∀ t, scc.contains t →
      s = t ∨ PathTo succs' (fun x => ¬ scc.contains x) s t := hconnected.domainBlocked
  have hanchor' : scc.contains anchor := (Std.HashSet.mem_iff_contains).mp hanchor
  obtain ⟨hne, hheadeq, -, hchain, hback, hcov⟩ :=
    stitchCycleAt_valid scc succs' edgeMarks numMarks anchor hcovers' hconn' hanchor'
      (stitchCycleAt scc succs' edgeMarks numMarks anchor) rfl
  refine ⟨{
    stem := stem
    cycle := stitchCycleAt scc succs' edgeMarks numMarks anchor
    stem_nonempty := List.length_pos_iff.mpr hstemne
    cycle_nonempty := List.length_pos_iff.mpr hne
    stem_head_initial := hstemhead
    stem_chain := hstemchain
    overlap := hstemlast.trans hheadeq.symm
    cycle_chain := fun i hi => (Array.mem_filter.mp (hchain i hi)).1
    cycle_back := (Array.mem_filter.mp hback).1
    cycle_covers_marks := hcov
  }, rfl, rfl⟩

/-- The same, with the cycle stitched inside a *subgraph* of the one the stem walks. The prune needs this:
a witness found in a pruned candidate has to have its cycle rebuilt inside that candidate's restricted
graph — an edge the region excludes is not one the reported options admit — while its stem comes from a BFS
over the ambient reachable set. -/
theorem stitchCycleAt_toTAcceptingCycle' [LawfulBEq State] [LawfulHashable State]
    {initialStates : List State} {succs g : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat}
    {scc : Std.HashSet State} {anchor : State} {stem : List State}
    (hg : ∀ a b, b ∈ g a → b ∈ succs a)
    (hconnected : InternallyConnected g scc) (hcovers : AcceptingMarks g edgeMarks numMarks scc)
    (hanchor : anchor ∈ scc) (hstemne : stem ≠ []) (hstemhead : stem.head hstemne ∈ initialStates)
    (hstemchain : ∀ i, (hi : i + 1 < stem.length) → stem[i + 1] ∈ succs stem[i])
    (hstemlast : stem.getLast hstemne = anchor) :
    ∃ ac : TAcceptingCycle initialStates succs edgeMarks numMarks, ac.stem = stem ∧
      ac.cycle = stitchCycleAt scc (sccSuccs g scc) edgeMarks numMarks anchor := by
  set g' := sccSuccs g scc with hg'def
  have hcovers' : AcceptingMarks g' edgeMarks numMarks scc := hcovers.sccSuccs
  have hconn' : ∀ s, scc.contains s → ∀ t, scc.contains t →
      s = t ∨ PathTo g' (fun x => ¬ scc.contains x) s t := hconnected.domainBlocked
  have hanchor' : scc.contains anchor := (Std.HashSet.mem_iff_contains).mp hanchor
  obtain ⟨hne, hheadeq, -, hchain, hback, hcov⟩ :=
    stitchCycleAt_valid scc g' edgeMarks numMarks anchor hcovers' hconn' hanchor'
      (stitchCycleAt scc g' edgeMarks numMarks anchor) rfl
  refine ⟨{
    stem := stem
    cycle := stitchCycleAt scc g' edgeMarks numMarks anchor
    stem_nonempty := List.length_pos_iff.mpr hstemne
    cycle_nonempty := List.length_pos_iff.mpr hne
    stem_head_initial := hstemhead
    stem_chain := hstemchain
    overlap := hstemlast.trans hheadeq.symm
    cycle_chain := fun i hi => hg _ _ (Array.mem_filter.mp (hchain i hi)).1
    cycle_back := hg _ _ (Array.mem_filter.mp hback).1
    cycle_covers_marks := hcov
  }, rfl, rfl⟩

end LTLLib
