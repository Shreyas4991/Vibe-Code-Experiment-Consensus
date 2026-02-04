import Mathlib
import Consensus.NetworkWithCrash

namespace Consensus

structure ConsensusSpec (Input Output Internal Val : Type u) where
  decide : Action Input Output Internal → Option Val
  propose : Action Input Output Internal → Option Val

def DecidesAt {n : Nat} {Input Output Internal Val : Type u}
    (spec : ConsensusSpec Input Output Internal Val)
    (tr : Stream' (Fin n × Option (Action Input Output Internal)))
    (i : Fin n) (v : Val) : Prop :=
  ∃ m a, (tr m).1 = i ∧ (tr m).2 = some a ∧ spec.decide a = some v

def Proposes {n : Nat} {Input Output Internal Val : Type u}
    (spec : ConsensusSpec Input Output Internal Val)
    (tr : Stream' (Fin n × Option (Action Input Output Internal)))
    (v : Val) : Prop :=
  ∃ m a, (tr m).2 = some a ∧ spec.propose a = some v

def StrongValidity {n : Nat} {Input Output Internal Val : Type u}
    (spec : ConsensusSpec Input Output Internal Val)
    (tr : Stream' (Fin n × Option (Action Input Output Internal))) : Prop :=
  ∀ i v, DecidesAt spec tr i v → Proposes spec tr v

def Agreement {n : Nat} {Input Output Internal Val : Type u}
    (spec : ConsensusSpec Input Output Internal Val)
    (tr : Stream' (Fin n × Option (Action Input Output Internal))) : Prop :=
  ∀ i j v w, DecidesAt spec tr i v → DecidesAt spec tr j w → v = w

def Termination {n : Nat} {Input Output Internal Val : Type u}
    (spec : ConsensusSpec Input Output Internal Val)
    (tr : Stream' (Fin n × Option (Action Input Output Internal))) : Prop :=
  ∀ i, ∃ v, DecidesAt spec tr i v

def ImplementsConsensus {n : Nat} {State Input Output Internal Mem Val : Type u}
    (spec : ConsensusSpec Input Output Internal Val)
    (C : Network.NetConfig n State Input Output Internal Mem Val) : Prop :=
  ∀ tr, Network.NetTraceInfCrash C tr →
    StrongValidity spec tr ∧ Agreement spec tr ∧ Termination spec tr

end Consensus
