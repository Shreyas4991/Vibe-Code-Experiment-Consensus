import Mathlib
import Consensus.Network

namespace Consensus

/-- A wait-free trace: every finite prefix is a valid trace and every process
appears infinitely often. -/
def WaitFreeTrace {n : Nat} {State Input Output Internal Mem : Type u}
    (N : Network n State Input Output Internal Mem)
    (tr : Stream' (Fin n × Action Input Output Internal)) : Prop :=
  (∀ k, Network.NetTrace N (Stream'.take k tr)) ∧
  (∀ i k, ∃ m ≥ k, (tr m).1 = i)

/-- A wait-free infinite trace: a valid infinite execution with fair per-process scheduling. -/
def WaitFreeTraceInf {n : Nat} {State Input Output Internal Mem : Type u}
    (N : Network n State Input Output Internal Mem)
    (tr : Stream' (Fin n × Action Input Output Internal)) : Prop :=
  Network.NetTraceInf N tr ∧
  (∀ i k, ∃ m ≥ k, (tr m).1 = i)

/-- Prefix-closedness for infinite traces: every finite prefix is a valid network trace. -/
def PrefixClosedInf {n : Nat} {State Input Output Internal Mem : Type u}
    (N : Network n State Input Output Internal Mem)
    (tr : Stream' (Fin n × Action Input Output Internal)) : Prop :=
  ∀ k, Network.NetTrace N (Stream'.take k tr)

/-- External fairness: each process performs infinitely many external events. -/
def FairExternal {n : Nat} {State Input Output Internal Mem : Type u}
    (N : Network n State Input Output Internal Mem)
    (tr : Stream' (Fin n × Action Input Output Internal)) : Prop :=
  Network.NetTraceInf N tr ∧
  ∀ i k, ∃ m ≥ k, (tr m).1 = i ∧ Network.eventExternal (tr m).2

/-- Quiescence: after some point, only internal actions occur. -/
def Quiescent {n : Nat} {State Input Output Internal Mem : Type u}
    (N : Network n State Input Output Internal Mem)
    (tr : Stream' (Fin n × Action Input Output Internal)) : Prop :=
  Network.NetTraceInf N tr ∧
  ∃ k, ∀ m ≥ k, ¬ Network.eventExternal (tr m).2

/-- Stutter invariance: adding a finite prefix of internal actions preserves a property. -/
def StutterInvariant {n : Nat} {Input Output Internal : Type u}
    (P : Stream' (Fin n × Action Input Output Internal) → Prop) : Prop :=
  ∀ tr i (ls : List Internal),
    P tr →
    P (Stream'.appendStream' (ls.map fun a => (i, Action.internal a)) tr)

end Consensus
