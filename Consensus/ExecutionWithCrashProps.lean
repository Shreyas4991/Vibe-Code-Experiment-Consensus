import Mathlib
import Consensus.NetworkWithCrash

namespace Consensus

/-- A wait-free trace with crashes: every finite prefix is a valid crash-aware trace and every
process appears infinitely often (ignoring whether the step is a crash or an action). -/
def WaitFreeTraceCrash {n : Nat} {State Input Output Internal Mem Val : Type u}
    (C : Network.NetConfig n State Input Output Internal Mem Val)
    (tr : Stream' (Fin n × Option (Action Input Output Internal))) : Prop :=
  (∀ k, Network.NetTraceCrash C (Stream'.take k tr)) ∧
  (∀ i k, ∃ m ≥ k, (tr m).1 = i)

/-- A wait-free infinite trace with crashes: a valid infinite crash-aware execution with fair
per-process scheduling. -/
def WaitFreeTraceInfCrash {n : Nat} {State Input Output Internal Mem Val : Type u}
    (C : Network.NetConfig n State Input Output Internal Mem Val)
    (tr : Stream' (Fin n × Option (Action Input Output Internal))) : Prop :=
  Network.NetTraceInfCrash C tr ∧
  (∀ i k, ∃ m ≥ k, (tr m).1 = i)

/-- Prefix-closedness for infinite crash-aware traces: every finite prefix is a valid trace. -/
def PrefixClosedInfCrash {n : Nat} {State Input Output Internal Mem Val : Type u}
    (C : Network.NetConfig n State Input Output Internal Mem Val)
    (tr : Stream' (Fin n × Option (Action Input Output Internal))) : Prop :=
  ∀ k, Network.NetTraceCrash C (Stream'.take k tr)

/-- External fairness with crashes: each process performs infinitely many external actions
(ignoring crash steps). -/
def FairExternalCrash {n : Nat} {State Input Output Internal Mem Val : Type u}
    (C : Network.NetConfig n State Input Output Internal Mem Val)
    (tr : Stream' (Fin n × Option (Action Input Output Internal))) : Prop :=
  Network.NetTraceInfCrash C tr ∧
  ∀ i k, ∃ m ≥ k, (tr m).1 = i ∧
    match (tr m).2 with
    | some a => Network.eventExternal a
    | none => False

/-- Quiescence with crashes: after some point, no external actions occur. -/
def QuiescentCrash {n : Nat} {State Input Output Internal Mem Val : Type u}
    (C : Network.NetConfig n State Input Output Internal Mem Val)
    (tr : Stream' (Fin n × Option (Action Input Output Internal))) : Prop :=
  Network.NetTraceInfCrash C tr ∧
  ∃ k, ∀ m ≥ k,
    match (tr m).2 with
    | some a => ¬ Network.eventExternal a
    | none => True

/-- Stutter invariance with crashes: adding a finite prefix of internal actions
preserves a property. -/
def StutterInvariantCrash {n : Nat} {Input Output Internal : Type u}
    (P : Stream' (Fin n × Option (Action Input Output Internal)) → Prop) : Prop :=
  ∀ tr i (ls : List Internal),
    P tr →
    P (Stream'.appendStream' (ls.map fun a => (i, some (Action.internal a))) tr)

end Consensus
