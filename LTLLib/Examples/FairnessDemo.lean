/-
  This file demonstrates the state-space blowup caused by introducing fairness hypothesis.

  As a running example: Dining Philosophers

  3 philosophers on a round table, 3 spoons
  - Each philosopher is thinking, until at any point: They pick up both forks and start eating.
  - They eat for some time, before putting the forks down and thinking again.

  Q: Can it be that philosopher 0 starves?
  - Yes: Philosopher 1 & 2 continuously trade forks, never allowing philosopher 0 to eat (Starvation/Livelock)
  - In formulations where each philosopher picks up their right fork first then the left fork,
    we can even run into a deadlock: Each philosopher picks up their right fork at the same time

  Fairness:
  - Weak fairness not enough to prevent starvation, as philosopher 0 keeps switching between being
    able to eat or not ("eat" action is never continuously enabled)
  - Strong fairness: Philosopher 0 must eventually eat.
-/
import LTLLib.Examples.BuildPrint

namespace LTLLib.Examples

abbrev Prop' := String

def ψWeak : Formula Prop' :=
  .weakFairness (.atom "enabledEat0") (.atom "takenEat0")

def ψStrong : Formula Prop' :=
  .strongFairness (.atom "enabledEat0") (.atom "takenEat0")

def φ : Formula Prop' :=
  .eventually (.atom "phil0eats")


#eval runExample φ                    /-  3 GBA states,  3 BA states -/
#eval runExample (.implies ψWeak φ)   /- 10 GBA states, 20 BA states -/
#eval runExample (.implies ψStrong φ) /- 14 GBA states, 42 BA states -/

end LTLLib.Examples
