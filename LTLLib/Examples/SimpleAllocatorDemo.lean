/-
  Real world example of how limiting fairness can be.
  Here we model an LTL formula from "SimpleAllocator" in the TLA+ examples: "ClientsWillObtain"
    - In the Veil examples folder, this is called "clientsWillObtainFair" in SimpleAllocator.lean.
  Fairness is modelled as 3 conjuncts: Non-stuttering infinitely, weak-fairness, strong-fairness

  TLA+ definitions:

  SimpleAllocator ==
    /\ Init /\ [][Next]_vars
    /\ \A c \in Clients: WF_vars(Return(c, alloc[c]))
    /\ \A c \in Clients: SF_vars(\E S \in SUBSET Resources: Allocate(c,S))

  ClientsWillObtain ==
    \A c \in Clients, r \in Resources : r \in unsat[c] ~> r \in alloc[c]

-/
import LTLLib.Examples.BuildPrint

namespace LTLLib.Examples

abbrev Prop' := String


def φ0 : Formula Prop' := .unconditionalFairness (.atom "non-stutter") -- Not actually required in the SimpleAllocator model, for Demo purpose
def φ1 : Formula Prop' := .weakFairness (.atom "Enabled(Return(c, alloc[c]))") (.atom "Taken(Return(c, alloc[c]))")
def φ2 : Formula Prop' := .strongFairness (.atom "Enabled(Allocate(c,S))") (.atom "Taken(Allocate(c,S))")
def φ3 : Formula Prop' := .always (.implies (.atom "r in unsat[c]") (.eventually (.atom "r in alloc[c]")))

#eval runExample (.implies (.and (φ0) (.and (φ1) (φ2))) (φ3))               /- GBA: 32  / BA: 160   -/
--#eval runExample (.not (.implies (.and (φ0) (.and (φ1) (φ2))) (φ3)))      /- GBA: 496 / BA: 2976  -/

end LTLLib.Examples
