import Mathlib
import Consensus.ConsensusSpec

namespace Consensus

/-- A configuration is univalent for value `v` if any decision in any execution decides `v`. -/
def Univalent {n : Nat} {State Input Output Internal Mem Val : Type u}
    (spec : ConsensusSpec Input Output Internal Val)
    (C : Network.NetConfig n State Input Output Internal Mem Val) (v : Val) : Prop :=
  ∀ tr, Network.NetTraceInfCrash C tr →
    ∀ i v', DecidesAt spec tr i v' → v' = v

/-- A configuration is bivalent if it has executions that decide two distinct values. -/
def Bivalent {n : Nat} {State Input Output Internal Mem Val : Type u}
    (spec : ConsensusSpec Input Output Internal Val)
    (C : Network.NetConfig n State Input Output Internal Mem Val) : Prop :=
  ∃ v w, v ≠ w ∧
    (∃ tr i, Network.NetTraceInfCrash C tr ∧ DecidesAt spec tr i v) ∧
    (∃ tr i, Network.NetTraceInfCrash C tr ∧ DecidesAt spec tr i w)

theorem Univalent.decides_eq {n : Nat} {State Input Output Internal Mem Val : Type u}
    {spec : ConsensusSpec Input Output Internal Val}
    {C : Network.NetConfig n State Input Output Internal Mem Val}
    {tr : Stream' (Fin n × Option (Action Input Output Internal))}
    {i : Fin n} {v v' : Val} :
    Univalent spec C v →
    Network.NetTraceInfCrash C tr →
    DecidesAt spec tr i v' →
    v' = v := by
  intro h htr hdec
  exact h tr htr i v' hdec

theorem Univalent.unique_of_decision {n : Nat} {State Input Output Internal Mem Val : Type u}
    {spec : ConsensusSpec Input Output Internal Val}
    {C : Network.NetConfig n State Input Output Internal Mem Val}
    {tr : Stream' (Fin n × Option (Action Input Output Internal))}
    {i : Fin n} {u v w : Val} :
    Univalent spec C v →
    Univalent spec C w →
    Network.NetTraceInfCrash C tr →
    DecidesAt spec tr i u →
    v = w := by
  intro hv hw htr hdec
  have hv' : u = v := hv tr htr i u hdec
  have hw' : u = w := hw tr htr i u hdec
  exact hv'.symm.trans hw'

theorem Bivalent.not_univalent {n : Nat} {State Input Output Internal Mem Val : Type u}
    {spec : ConsensusSpec Input Output Internal Val}
    {C : Network.NetConfig n State Input Output Internal Mem Val}
    {v : Val} :
    Bivalent spec C → ¬ Univalent spec C v := by
  intro hb hu
  rcases hb with ⟨v1, w1, hne, ⟨tr1, i1, htr1, hdec1⟩, ⟨tr2, i2, htr2, hdec2⟩⟩
  by_cases hv : v = v1
  · subst hv
    have := hu tr2 htr2 i2 w1 hdec2
    exact hne (this.symm)
  · have := hu tr1 htr1 i1 v1 hdec1
    exact hv (this.symm)

theorem Bivalent.exists_decision {n : Nat} {State Input Output Internal Mem Val : Type u}
    {spec : ConsensusSpec Input Output Internal Val}
    {C : Network.NetConfig n State Input Output Internal Mem Val} :
    Bivalent spec C →
    ∃ tr i v, Network.NetTraceInfCrash C tr ∧ DecidesAt spec tr i v := by
  intro hb
  rcases hb with ⟨v, _w, _hne, ⟨tr, i, htr, hdec⟩, _⟩
  exact ⟨tr, i, v, htr, hdec⟩

end Consensus
