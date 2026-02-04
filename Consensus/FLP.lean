import Mathlib
import Consensus.ConsensusSpec
import Consensus.Bivalence
import Consensus.Initial

namespace Consensus

def FLP_Impossibility {n : Nat} {State Input Output Internal Mem Val : Type u}
    (spec : ConsensusSpec Input Output Internal Val)
    (C : Network.NetConfig n State Input Output Internal Mem Val) : Prop :=
  ¬ ImplementsConsensus spec C

/-- Bivalence is preserved by at least one admissible step. -/
theorem BivalentExtension {n : Nat} {State Input Output Internal Mem Val : Type u}
    (spec : ConsensusSpec Input Output Internal Val)
    (C : Network.NetConfig n State Input Output Internal Mem Val) :
    Bivalent spec C →
      ∃ lbl C', Network.NetStepWithCrash C lbl C' ∧ Bivalent spec C' := by
  admit

/-- Critical step lemma: non-commuting steps cannot force univalence. -/
theorem CriticalStep {n : Nat} {State Input Output Internal Mem Val : Type u}
    (spec : ConsensusSpec Input Output Internal Val)
    (C : Network.NetConfig n State Input Output Internal Mem Val) :
    Bivalent spec C →
      ∀ lbl1 lbl2 C1 C2,
        Network.NetStepWithCrash C lbl1 C1 →
        Network.NetStepWithCrash C lbl2 C2 →
        lbl1.1 ≠ lbl2.1 →
        (∃ v, Univalent spec C1 v) → False := by
  admit

/-- Infinite non-deciding execution constructed from bivalent extension steps. -/
theorem InfiniteBivalentExec {n : Nat} {State Input Output Internal Mem Val : Type u}
    (spec : ConsensusSpec Input Output Internal Val)
    (C : Network.NetConfig n State Input Output Internal Mem Val) :
    ∃ tr, Network.NetTraceInfCrash C tr ∧ Bivalent spec C := by
  admit

end Consensus
