/-
  Very weak alternating co-Büchi automata over arbitrary states, following `[GO01]` Definition 3 and the run notion of
  `[JN18]` section 2 (HOL4 `alterAScript`), stated over `OmegaWord α`, so no finite alphabet and no `[HOL4-ltl]`
  `word_range` side conditions are needed. Very weakness is a rank into `Nat`, `[TV21]` Lemma 3's condition C2 in rank form, so the state
  type needs no finiteness assumption.

  A run is a level-indexed state set with, per level and live state, the successor set its chosen transition committed to,
  `[GO01]`'s DAG with at most one node per state per level. Runs carry `[HOL4-ltl]`'s no-orphan clause, which run union
  and the level shift need to extend a branch back to level 0, while `succ` is constrained only at live states.

  Defines:
  - `VWAA`: guard/successor-set transitions, initial alternatives, co-Büchi finals and the very weak rank
  - `VWAA.Run`, `VWAA.Run.ValidFrom`: levels plus committed successor sets, and validity on a word from a level-0 set
  - `VWAA.Run.InfBranch`, `VWAA.StabilizesAt`: an infinite path through a run, and one eventually constant
  - `VWAA.Run.restrict`: the sub-run reachable from a subset of level 0
  - `VWAA.Run.conj`: two runs on one word merged with node sharing
  - `VWAA.Run.shift`, `VWAA.Run.prepend`: `r` with level 0 dropped, and `r` preceded by a fresh level
  - `VWAA.AcceptingRun`: co-Büchi acceptance, every branch meets `final` only finitely often
  - `VWAA.AcceptsFrom`, `VWAA.Accepts`: the language read from a level-0 set, and the automaton's language

  References:
  - `[GO01]` Gastin, Oddoux. Fast LTL to Büchi Automata Translation. CAV'01, LNCS 2102, Definition 3.
  - `[TV21]` Tsay, Vardi. From Linear Temporal Logics to Büchi Automata. LNCS 13030, Lemma 3 and Definition 6.
  - `[JN18]` Jantsch, Norrish. Verifying the LTL to Büchi Automata Translation via Very Weak Alternating
    Automata. ITP'18, section 2, with the HOL4 development's `alterAScript`.

  Sections:
  - The automaton
  - Runs
  - Run restriction
  - Run union
  - Level shift
  - Acceptance
-/
import LTLLib.LTL.Semantics
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Set.Finite.Basic

namespace LTLLib

universe u v

/-! ## The automaton -/

/-- A very weak alternating co-Büchi automaton. -/
structure VWAA (Q : Type v) (α : Type u) [DecidableEq Q] where
  -- guard/successor-set alternatives, the successor set of a taken transition is conjunctive
  trans : Q → List (((α → Prop) → Prop) × Finset Q)
  -- the alternatives for level 0, a run picks one
  initial : List (Finset Q)
  -- co-Büchi: a branch may meet these only finitely often
  final : Q → Prop
  -- the very weak rank, `[TV21]` Lemma 3's condition C2 in rank form
  rank : Q → Nat
  veryWeak : ∀ q g O, (g, O) ∈ trans q → ∀ q' ∈ O, q' = q ∨ rank q' < rank q

/-! ## Runs -/

/-- A run: `level i` are the states alive at step `i`, and `succ i q` is the successor set that `q`'s chosen
transition at step `i` committed to. -/
structure VWAA.Run (Q : Type v) where
  level : Nat → Finset Q
  succ : Nat → Q → Finset Q

variable {Q : Type v} {α : Type u} [DecidableEq Q]

/-- `r` is a run of `A` on `ξ` from `S`: every live state takes an enabled transition, its committed successors are alive
on the next level, and nothing is alive without being spawned (`[HOL4-ltl]`'s no-orphan clause). -/
structure VWAA.Run.ValidFrom (r : VWAA.Run Q) (A : VWAA Q α) (S : Finset Q) (ξ : OmegaWord α) : Prop where
  init : r.level 0 = S
  step : ∀ i q, q ∈ r.level i → ∃ g, (g, r.succ i q) ∈ A.trans q ∧ g (ξ i)
  succ_sub : ∀ i q, q ∈ r.level i → r.succ i q ⊆ r.level (i + 1)
  no_orphan : ∀ i q, q ∈ r.level (i + 1) → ∃ p ∈ r.level i, q ∈ r.succ i p

/-- An infinite branch of a run, following the committed successor sets from level 0 on. -/
def VWAA.Run.InfBranch (r : VWAA.Run Q) (b : Nat → Q) : Prop :=
  b 0 ∈ r.level 0 ∧ ∀ i, b (i + 1) ∈ r.succ i (b i)

/-- The branch is constantly `q` from some level on. -/
def VWAA.StabilizesAt (b : Nat → Q) (q : Q) : Prop := ∃ i, ∀ m, i ≤ m → b m = q

/-! ## Run restriction -/

/-- The levels of `r` reachable from `S`: level 0 is `S`, and each later level keeps only what the surviving
states committed to. -/
def VWAA.Run.restrictLevel (r : VWAA.Run Q) (S : Finset Q) : Nat → Finset Q
  | 0 => S
  | i + 1 => (r.restrictLevel S i).biUnion fun q => r.succ i q

/-- `r` cut down to the part reachable from `S`, with `succ` unchanged, `[HOL4-ltl]`'s `run_restr`. -/
def VWAA.Run.restrict (r : VWAA.Run Q) (S : Finset Q) : VWAA.Run Q where
  level := r.restrictLevel S
  succ := r.succ

/-! ## Run union -/

/-- The union's successor choice, the first run's wherever it claims the state, `[GO01]`'s node sharing. -/
def VWAA.Run.conjSucc (x y : VWAA.Run Q) (i : Nat) (q : Q) : Finset Q :=
  if q ∈ x.level i then x.succ i q else y.succ i q

/-- The union's levels, generated from the two level-0 sets, since unioning level by level would leave orphans. -/
def VWAA.Run.conjLevel (x y : VWAA.Run Q) : Nat → Finset Q
  | 0 => x.level 0 ∪ y.level 0
  | i + 1 => (x.conjLevel y i).biUnion (x.conjSucc y i)

/-- `[HOL4-ltl]`'s `conj_run`: two runs on the same word merged into one, sharing a node wherever both reach it. -/
def VWAA.Run.conj (x y : VWAA.Run Q) : VWAA.Run Q where
  level := x.conjLevel y
  succ := x.conjSucc y

/-! ## Level shift -/

/-- `r` with level 0 dropped and the rest re-indexed, the run entered one letter later. -/
def VWAA.Run.shift (r : VWAA.Run Q) : VWAA.Run Q where
  level i := r.level (i + 1)
  succ i := r.succ (i + 1)

/-- The levels of `r.prepend S succ0`: a fresh level `S` first, then `r`'s own levels. -/
def VWAA.Run.prependLevel (r : VWAA.Run Q) (S : Finset Q) : Nat → Finset Q
  | 0 => S
  | i + 1 => r.level i

/-- The successor sets of `r.prepend S succ0`: `succ0` at the fresh level, `r.succ` after. -/
def VWAA.Run.prependSucc (r : VWAA.Run Q) (succ0 : Q → Finset Q) : Nat → Q → Finset Q
  | 0 => succ0
  | i + 1 => r.succ i

/-- `r` preceded by a fresh level `S` whose states commit to `succ0`, the run entered one letter earlier,
`[HOL4-ltl]`'s `REPL_RUN_CONSTR_LEMM`. -/
def VWAA.Run.prepend (r : VWAA.Run Q) (S : Finset Q) (succ0 : Q → Finset Q) : VWAA.Run Q where
  level := r.prependLevel S
  succ := r.prependSucc succ0

/-! ## Acceptance -/

/-- Co-Büchi acceptance: every infinite branch meets `final` only finitely often. -/
def VWAA.AcceptingRun (A : VWAA Q α) (r : VWAA.Run Q) : Prop :=
  ∀ b, r.InfBranch b → {i | A.final (b i)}.Finite

/-- The language of `A` read from the level-0 set `S`. -/
def VWAA.AcceptsFrom (A : VWAA Q α) (S : Finset Q) (ξ : OmegaWord α) : Prop :=
  ∃ r : VWAA.Run Q, r.ValidFrom A S ξ ∧ A.AcceptingRun r

/-- The language of `A`: some initial alternative accepts. -/
def VWAA.Accepts (A : VWAA Q α) (ξ : OmegaWord α) : Prop :=
  ∃ S ∈ A.initial, A.AcceptsFrom S ξ

end LTLLib
