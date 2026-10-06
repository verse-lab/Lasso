"""
Python counterpart to FairnessDemo.lean: demonstrates the state-space
blowup caused by introducing fairness hypotheses, using the Spot library
instead of LTLLib's own tableau construction.

As a running example: Dining Philosophers

3 philosophers on a round table, 3 spoons
- Each philosopher is thinking, until at any point: They pick up both forks
  and start eating.
- They eat for some time, before putting the forks down and thinking again.

Q: Can it be that philosopher 0 starves?
- Yes: Philosopher 1 & 2 continuously trade forks, never allowing
  philosopher 0 to eat (Starvation/Livelock)
- In formulations where each philosopher picks up their right fork first
  then the left fork, we can even run into a deadlock: Each philosopher
  picks up their right fork at the same time

Fairness:
- Weak fairness not enough to prevent starvation, as philosopher 0 keeps
  switching between being able to eat or not ("eat" action is never
  continuously enabled)
- Strong fairness: Philosopher 0 must eventually eat.

Where FairnessDemo.lean builds a GBA (via LTLLib's tableau construction)
and then degeneralizes it to a BA, this script instead asks Spot to
translate straight to a TGBA (transition-based generalized Buchi
automaton) -- the representation Spot's translator is built around, and
the one modern LTL-to-automaton tools use in place of a state-based GBA.
"""

import spot


def weak_fairness(enabled: str, taken: str) -> str:
    """G(F(!enabled) | F(taken)): if `enabled` is continuously true, then
    `taken` must eventually become true."""
    return f"G(F(!{enabled}) | F({taken}))"


def strong_fairness(enabled: str, taken: str) -> str:
    """GF(enabled) -> GF(taken): if `enabled` is true infinitely often,
    then `taken` must be true infinitely often."""
    return f"(G F({enabled})) -> (G F({taken}))"


psi_weak = weak_fairness("enabledEat0", "takenEat0")
psi_strong = strong_fairness("enabledEat0", "takenEat0")
phi = "F(phil0eats)"


def print_tgba(aut: spot.twa_graph) -> str:
    """Render a TGBA's states, acceptance condition, and transitions
    (mirrors printGBA/printBA in BuildPrint.lean, but transition-labeled:
    Spot's TGBA carries its formula on each edge rather than on each
    state)."""
    bdict = aut.get_dict()
    state_line = f"states ({aut.num_states()}): {list(range(aut.num_states()))}"
    init_line = f"initial: {aut.get_init_state_number()}"
    acc_line = f"acceptance ({aut.num_sets()} sets): {aut.get_acceptance()}"
    trans_lines = []
    for s in range(aut.num_states()):
        for e in aut.out(s):
            cond = spot.bdd_format_formula(bdict, e.cond)
            marks = list(e.acc.sets())
            trans_lines.append(f"  {s} -> {e.dst} [{cond}] {{{','.join(map(str, marks))}}}")
    trans_lines.sort()
    return "\n".join(
        [state_line, init_line, acc_line, "transitions:"] + trans_lines
    )


def run_example(formula: str) -> None:
    """Parse `formula`, translate it straight to a TGBA, and print it
    (Spot's translate() combines what LTLLib splits into
    createGraph -> constructGBA -> GBA.degeneralize)."""
    f = spot.formula(formula)
    display = str(f)  # capture before translate(), which mutates f in place
    aut = spot.translate(f, "TGBA")
    print(f"phi = {display}")
    print("\n== TGBA (spot.translate) ==")
    print(print_tgba(aut))


if __name__ == "__main__":
    run_example(phi)                                    #  2 TGBA states
    print("\n" + "=" * 60 + "\n")
    run_example(f"({psi_weak}) -> ({phi})")               #  3 TGBA states
    print("\n" + "=" * 60 + "\n")
    run_example(f"({psi_strong}) -> ({phi})")             #  3 TGBA states
