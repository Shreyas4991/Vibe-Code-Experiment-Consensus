import Mathlib
import Consensus.ConsensusSpec
import Consensus.Bivalence
import Consensus.IndistinguishableExecutions

namespace Consensus

def Initial {n : Nat} {State Input Output Internal Mem Val : Type u}
    (C : Network.NetConfig n State Input Output Internal (Option Mem) Val) : Prop :=
  (∀ i, C.net.state i ∈ (C.net.automata i).start) ∧
  (∀ i, C.net.mem i = none) ∧
  (∀ i, C.status i = Network.NodeStatus.alive)

def NoCrashTrace {n : Nat} {Input Output Internal : Type u}
    (tr : Stream' (Fin n × Option (Action Input Output Internal))) : Prop :=
  ∀ k, (tr k).2.isSome

/-
Crash flip lemma (Lemma 3.7 step):
If two neighboring initial configurations differ only at node `j`'s input, then
crashing `j` yields indistinguishable executions for all other nodes, which
forces bivalence.
-/
theorem CrashFlip {n : Nat} {State Input Output Internal Mem Val : Type u}
    (spec : ConsensusSpec Input Output Internal Val)
    (C0 C1 : Network.NetConfig n State Input Output Internal (Option Mem) Val)
    (j : Fin n)
    (hind :
      Indistinguishable (S := (Finset.univ.erase j)) C0 C1)
    (huniv0 : Univalent spec C0 v0)
    (huniv1 : Univalent spec C1 v1)
    (hneq : v0 ≠ v1) :
    Bivalent spec C0 := by
  -- Proof sketch: crash `j` to make the two executions indistinguishable to all other nodes,
  -- then use the differing valencies to conclude bivalence.
  admit
/-
Lemma 3.7 (scaffolded):
Given a family of initial configurations `E j` indexed by a cut position `j`,
if the endpoints are `v0`- and `v1`-univalent and every `E j` is univalent for
either `v0` or `v1`, then there exists a neighboring pair `E j`, `E (j+1)` where
the valency changes. Assuming that such a neighboring change yields bivalence,
we conclude there is a bivalent execution without crashes.
Source : https://www.mpi-inf.mpg.de/fileadmin/inf/d1/teaching/winter15/tods/ToDS_03.pdf
-/
theorem Lemma3_7 {n : Nat} {State Input Output Internal Mem Val : Type u}
    [DecidableEq Val]
    (spec : ConsensusSpec Input Output Internal Val)
    (v0 v1 : Val) (hneq : v0 ≠ v1)
    (E : Nat → Network.NetConfig n State Input Output Internal (Option Mem) Val)
    (hinit : ∀ j ≤ n, Initial (E j))
    (huniv : ∀ j ≤ n, Univalent spec (E j) v0 ∨ Univalent spec (E j) v1)
    (hdec : ∀ j ≤ n, ∃ tr i v, Network.NetTraceInfCrash (E j) tr ∧ DecidesAt spec tr i v)
    (h0 : Univalent spec (E 0) v0)
    (hn : Univalent spec (E n) v1)
    (hflip :
      ∀ j, j < n →
        Univalent spec (E j) v0 →
        Univalent spec (E (j + 1)) v1 →
        Bivalent spec (E j)) :
    ∃ j, j < n ∧ Bivalent spec (E j) := by
  classical
  have hex : ∃ j, j ≤ n ∧ Univalent spec (E j) v1 := by
    exact ⟨n, le_rfl, hn⟩
  let j0 := Nat.find hex
  have hj0_le : j0 ≤ n := (Nat.find_spec hex).1
  have hj0_v1 : Univalent spec (E j0) v1 := (Nat.find_spec hex).2
  have hj0_ne0 : j0 ≠ 0 := by
    intro hzero
    have hv1 : Univalent spec (E 0) v1 := by simpa [hzero] using hj0_v1
    rcases hdec 0 (Nat.zero_le _) with ⟨tr, i, v, htr, hdec0⟩
    have hv0eq : v = v0 := h0 tr htr i v hdec0
    have hv1eq : v = v1 := hv1 tr htr i v hdec0
    exact hneq (hv0eq.symm.trans hv1eq)
  have hj0_pos : 0 < j0 := Nat.pos_of_ne_zero hj0_ne0
  have hjm1_lt : j0 - 1 < n := by
    have : j0 - 1 < j0 := Nat.sub_lt (Nat.pos_of_ne_zero hj0_ne0) (Nat.succ_pos _)
    exact lt_of_lt_of_le this hj0_le
  have hjm1_univ :
      Univalent spec (E (j0 - 1)) v0 := by
    have hcases := huniv (j0 - 1) (Nat.sub_le _ _)
    cases hcases with
    | inl hv0 => exact hv0
    | inr hv1 =>
        have : j0 = 0 := by
          have : j0 - 1 < j0 := Nat.sub_lt (Nat.pos_of_ne_zero hj0_ne0) (Nat.succ_pos _)
          exact False.elim (Nat.lt_asymm this (Nat.lt_of_lt_of_le this hj0_le))
        exact (False.elim (hj0_ne0 this))
  refine ⟨j0 - 1, hjm1_lt, ?_⟩
  have hj0_succ : j0 - 1 + 1 = j0 := Nat.sub_add_cancel hj0_pos
  have hnext : Univalent spec (E (j0 - 1 + 1)) v1 := by simpa [hj0_succ] using hj0_v1
  exact CrashFlip (j0 - 1) hjm1_lt hjm1_univ hnext



/-- From an initial configuration, there exists a decision trace. -/
theorem ExistsDecisionFromInitial {n : Nat} {State Input Output Internal Mem Val : Type u}
    (i0 : Fin n)
    (spec : ConsensusSpec Input Output Internal Val)
    (C0 : Network.NetConfig n State Input Output Internal (Option Mem) Val)
    (hcons : ImplementsConsensus spec C0)
    (v0 : Val)
    (htrace : ∃ tr, Network.NetTraceInfCrash C0 tr ∧ NoCrashTrace tr)
    (honly : ∀ tr v, Network.NetTraceInfCrash C0 tr → Proposes spec tr v → v = v0) :
    ∃ tr i, Network.NetTraceInfCrash C0 tr ∧ DecidesAt spec tr i v0 := by
  rcases htrace with ⟨tr, htr, _hno⟩
  have hspec := hcons tr htr
  rcases hspec with ⟨hvalid, _hagree, hterm⟩
  rcases hterm (i := i0) with ⟨v, hdec⟩
  have hprop : Proposes spec tr v := hvalid i0 v hdec
  have hv : v = v0 := honly tr v htr hprop
  refine ⟨tr, i0, htr, ?_⟩
  simpa [hv] using hdec

/-- Distinct decisions from the two endpoint configurations of a cut family. -/
theorem ExistsDistinctDecisionsFromEndpoints {n : Nat}
  {State Input Output Internal Mem Val : Type u}
    (spec : ConsensusSpec Input Output Internal Val)
    (E : Nat → Network.NetConfig n State Input Output Internal (Option Mem) Val)
    (v0 v1 : Val) (hneq : v0 ≠ v1)
    (hdec0 : ∃ tr i, Network.NetTraceInfCrash (E 0) tr ∧ DecidesAt spec tr i v0)
    (hdec1 : ∃ tr i, Network.NetTraceInfCrash (E (n - 1)) tr ∧ DecidesAt spec tr i v1) :
    ∃ v0 v1, v0 ≠ v1 ∧
      (∃ tr i, Network.NetTraceInfCrash (E 0) tr ∧ DecidesAt spec tr i v0) ∧
      (∃ tr i, Network.NetTraceInfCrash (E (n - 1)) tr ∧ DecidesAt spec tr i v1) := by
  exact ⟨v0, v1, hneq, hdec0, hdec1⟩

/-- There exists a bivalent initial configuration from the cut family. -/
theorem ExistsBivalentInitialFromLemma3_7 {n : Nat} {State Input Output Internal Mem Val : Type u}
    [DecidableEq Val]
    (spec : ConsensusSpec Input Output Internal Val)
    (v0 v1 : Val) (hneq : v0 ≠ v1)
    (E : Nat → Network.NetConfig n State Input Output Internal (Option Mem) Val)
    (hinit : ∀ j ≤ n, Initial (E j))
    (huniv : ∀ j ≤ n, Univalent spec (E j) v0 ∨ Univalent spec (E j) v1)
    (hdec : ∀ j ≤ n, ∃ tr i v, Network.NetTraceInfCrash (E j) tr ∧ DecidesAt spec tr i v)
    (h0 : Univalent spec (E 0) v0)
    (hn : Univalent spec (E n) v1)
    (hflip :
      ∀ j, j < n →
        Univalent spec (E j) v0 →
        Univalent spec (E (j + 1)) v1 →
        Bivalent spec (E j)) :
    ∃ j, j < n ∧ Bivalent spec (E j) := by
  exact Lemma3_7 (spec := spec) (v0 := v0) (v1 := v1) hneq E hinit huniv
    hdec h0 hn hflip

/-- There exists a bivalent initial configuration. -/
theorem ExistsBivalentInitial {n : Nat} {State Input Output Internal Mem Val : Type u}
    [DecidableEq Val]
    (spec : ConsensusSpec Input Output Internal Val)
    (E : Nat → Network.NetConfig n State Input Output Internal (Option Mem) Val)
    (v0 v1 : Val) (hneq : v0 ≠ v1)
    (hinit : ∀ j ≤ n, Initial (E j))
    (huniv : ∀ j ≤ n, Univalent spec (E j) v0 ∨ Univalent spec (E j) v1)
    (hdec : ∀ j ≤ n, ∃ tr i v, Network.NetTraceInfCrash (E j) tr ∧ DecidesAt spec tr i v)
    (h0 : Univalent spec (E 0) v0)
    (hn : Univalent spec (E n) v1)
    (hflip :
      ∀ j, j < n →
        Univalent spec (E j) v0 →
        Univalent spec (E (j + 1)) v1 →
        Bivalent spec (E j)) :
    ∃ j, j < n ∧ Bivalent spec (E j) := by
  exact ExistsBivalentInitialFromLemma3_7 (spec := spec) (v0 := v0) (v1 := v1)
    hneq E hinit huniv hdec h0 hn hflip

end Consensus
