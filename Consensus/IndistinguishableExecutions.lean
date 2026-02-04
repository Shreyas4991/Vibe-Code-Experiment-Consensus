import Mathlib
import Consensus.NetworkWithCrash

namespace Consensus

/-- Two configurations are indistinguishable to a set of nodes `S`. -/
def Indistinguishable {n : Nat} {State Input Output Internal Mem Val : Type u}
    (S : Finset (Fin n))
    (C C' : Network.NetConfig n State Input Output Internal Mem Val) : Prop :=
  C.net.automata = C'.net.automata ∧
  (∀ i, i ∈ S → C.net.state i = C'.net.state i) ∧
  (∀ i, i ∈ S → C.net.mem i = C'.net.mem i) ∧
  (∀ i, i ∈ S → C.status i = C'.status i) ∧
  (∀ i, i ∈ S → C.input i = C'.input i)

theorem Indistinguishable.refl {n : Nat} {State Input Output Internal Mem Val : Type u}
    (S : Finset (Fin n))
    (C : Network.NetConfig n State Input Output Internal Mem Val) :
    Indistinguishable S C C := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> intro i hi <;> rfl

theorem Indistinguishable.symm {n : Nat} {State Input Output Internal Mem Val : Type u}
    {S : Finset (Fin n)}
    {C C' : Network.NetConfig n State Input Output Internal Mem Val} :
    Indistinguishable S C C' → Indistinguishable S C' C := by
  rintro ⟨ha, hs, hm, hst, hin⟩
  refine ⟨ha.symm, ?_, ?_, ?_, ?_⟩
  · intro i hi; exact (hs i hi).symm
  · intro i hi; exact (hm i hi).symm
  · intro i hi; exact (hst i hi).symm
  · intro i hi; exact (hin i hi).symm

theorem Indistinguishable.trans {n : Nat} {State Input Output Internal Mem Val : Type u}
    {S : Finset (Fin n)}
    {C C' C'' : Network.NetConfig n State Input Output Internal Mem Val} :
    Indistinguishable S C C' → Indistinguishable S C' C'' → Indistinguishable S C C'' := by
  rintro ⟨ha1, hs1, hm1, hst1, hin1⟩ ⟨ha2, hs2, hm2, hst2, hin2⟩
  refine ⟨ha1.trans ha2, ?_, ?_, ?_, ?_⟩
  · intro i hi; exact (hs1 i hi).trans (hs2 i hi)
  · intro i hi; exact (hm1 i hi).trans (hm2 i hi)
  · intro i hi; exact (hst1 i hi).trans (hst2 i hi)
  · intro i hi; exact (hin1 i hi).trans (hin2 i hi)

theorem Indistinguishable.live_step {n : Nat} {State Input Output Internal Mem Val : Type u}
    {S : Finset (Fin n)}
    {C C' : Network.NetConfig n State Input Output Internal Mem Val}
    {i : Fin n} {a : Action Input Output Internal} :
    i ∉ S →
    Network.LiveStep C C' i a →
    Indistinguishable S C C' := by
  intro hnot hstep
  rcases hstep with ⟨_hstat, hstat', hinput, hnet⟩
  dsimp [Network.NetStep] at hnet
  rcases hnet with ⟨hauto, hrest⟩
  simp [Indistinguishable]
  refine ⟨hauto, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hij : j ≠ i := by
      intro hji
      exact hnot (hji ▸ hj)
    exact (hstate j hij).symm
  · intro j hj
    have hij : j ≠ i := by
      intro hji
      exact hnot (hji ▸ hj)
    exact (hmem j hij).symm
  · intro j hj
    have hij : j ≠ i := by
      intro hji
      exact hnot (hji ▸ hj)
    simp [hstat', hij]
  · intro j hj
    simpa [hinput]

theorem Indistinguishable.crash_step {n : Nat} {State Input Output Internal Mem Val : Type u}
    {S : Finset (Fin n)}
    {C C' : Network.NetConfig n State Input Output Internal Mem Val}
    {i : Fin n} :
    i ∉ S →
    Network.CrashStep C C' i →
    Indistinguishable S C C' := by
  intro hnot hcrash
  rcases hcrash with ⟨_hstat, hnet, hinput, hstat'⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [hnet]
  · intro j hj; simpa [hnet]
  · intro j hj; simpa [hnet]
  · intro j _hj
    simpa [hstat']
  · intro j _hj
    simpa [hinput]

end Consensus
