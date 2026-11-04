module

/-
  Finite ultimately periodic words over a set of atoms, the words every translator in this folder is tested on.

  Defines:
  - `Lasso`: a stem followed by a nonempty loop, one atom set per position, the word `stem · loop^ω`
  - `Lasso.size`, `Lasso.wordAt`, `Lasso.next`: the underlying finite state graph
  - `Lasso.toOmegaWord`: the infinite word it denotes

  Sections:
  - Lasso words
-/
public import Std
public import Lasso.LTL.Semantics

public section

namespace Lasso.LTLtoTGBA.Tests

/-! ## Lasso words -/

/-- The ultimately periodic word `stem · loop^ω`. `loop` is meant to be nonempty, an empty one reads as the empty atom set. -/
structure Lasso (α : Type u) [BEq α] [Hashable α] where
  stem : Array (Std.HashSet α)
  loop : Array (Std.HashSet α)

namespace Lasso

variable {α : Type u} [BEq α] [Hashable α]

/-- Positions of the lasso, the stem followed by one traversal of the loop. -/
def size (l : Lasso α) : Nat := l.stem.size + l.loop.size

/-- The atoms holding at position `i`, any `i`, folding the loop through `%`. -/
def wordAt (l : Lasso α) (i : Nat) : Std.HashSet α :=
  if i < l.stem.size then l.stem.getD i (Std.HashSet.emptyWithCapacity 0)
  else l.loop.getD ((i - l.stem.size) % l.loop.size) (Std.HashSet.emptyWithCapacity 0)

/-- The successor of a position `i < l.size`, wrapping the last loop position back to its first. -/
def next (l : Lasso α) (i : Nat) : Nat :=
  if i + 1 < l.size then i + 1 else l.stem.size

/-- The infinite word `stem · loop^ω` this lasso denotes. -/
def toOmegaWord (l : Lasso α) : OmegaWord α := fun i a => (l.wordAt i).contains a

end Lasso

end Lasso.LTLtoTGBA.Tests
