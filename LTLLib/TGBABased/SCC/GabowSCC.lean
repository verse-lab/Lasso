/-
  Algorithm 4 — Gabow's SCC emptiness check: refines `GenericDFS.lean`'s abstract operations with an index-stack
  variant of Dijkstra's approach.

  Renault, Duret-Lutz, Kordon, Poitrenaud, "Three SCC-based Emptiness Checks for Generalized Büchi Automata"
  (LPAR-19, 2013), §3.2. See `TGBABased.md`.

  Deferred until after `DijkstraSCC.lean` is running and benchmarked. Algorithm spec transcribed
  below, see `TGBABased.md`'s "SCC algorithm refinements" section for the mechanics, including a note
  on `GET_STATUS`'s nesting as transcribed here.

  uf : union find of ⟨Q ∪{DeadState}⟩
  roots: rstack of ⟨root: int, acc: 2F ⟩
  uf.make set(DeadState)

  GET STATUS(q ∈ Q) → Status
    if uf.ufcontains(q)
      if uf.same_set(q, DeadState)
        return DEAD
    else
      return LIVE
    else
      return UNKNOWN

  PUSH(q ∈ Q) → Position
    uf.make_set(q)
    roots.push_trivial(dfs.size())
    return q

  UPDATE(acc ∈ 2^F, d ∈ Q)
    ⟨r , a ⟩ ← roots.pop()
    a ← a ∪ acc
    while ¬uf.same_set(dfs[r].pos, d)
      uf.unite(dfs[r].pos, d)
      ⟨r , la⟩ ← roots.pop()
      a ← a ∪ dfs[r].acc ∪ la
    roots.push_non_trivial(a, r, dfs.size() - 1)
    if a = F
      report counterexample found

    POP(s ∈ Step)
      if dfs.size() = roots.top_root()
      // An SCC has been found.
      roots.pop()
      uf.unite(s.pos, DeadState)
-/

namespace LTLLib

end LTLLib
