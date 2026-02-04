import Mathlib
import Consensus.IOAutomata

namespace Consensus

/-- A network of `n` identical IO automata with shared memory cells. -/
structure Network (n : Nat) (State Input Output Internal Mem : Type u) where
  automata : Fin n → IOAutomaton State Input Output Internal
  mem : Fin n → Mem
  state : Fin n → State

namespace Network

def globalState {n : Nat} {State Input Output Internal Mem : Type u}
    (N : Network n State Input Output Internal Mem) : Fin n → State :=
  N.state

def read {n : Nat} {State Input Output Internal Mem : Type u}
    (N : Network n State Input Output Internal Mem) (i : Fin n) : Mem :=
  N.mem i

def readAll {n : Nat} {State Input Output Internal Mem : Type u}
    (N : Network n State Input Output Internal Mem) : Fin n → Mem :=
  N.mem

def writeOwn {n : Nat} {State Input Output Internal Mem : Type u}
    (N : Network n State Input Output Internal Mem) (i : Fin n) (m : Mem) :
    Fin n → Mem := by
  classical
  exact fun j => if h : j = i then m else N.mem j

def NetStep {n : Nat} {State Input Output Internal Mem : Type u}
    (N N' : Network n State Input Output Internal Mem)
    (i : Fin n) (a : Action Input Output Internal) : Prop :=
  N.automata = N'.automata ∧
  (N.automata i).step (N.state i) a (N'.state i) ∧
  (∀ j, j ≠ i → N'.state j = N.state j) ∧
  (∀ j, j ≠ i → N'.mem j = N.mem j)


def eventAll {Input Output Internal : Type u}
    (_a : Action Input Output Internal) : Prop :=
  True

def eventExternal {Input Output Internal : Type u}
    (a : Action Input Output Internal) : Prop :=
  match a with
  | Action.inp _ => True
  | Action.out _ => True
  | Action.internal _ => False

inductive NetExec {n : Nat} {State Input Output Internal Mem : Type u} :
    Network n State Input Output Internal Mem →
    List (Fin n × Action Input Output Internal) →
    Network n State Input Output Internal Mem → Prop
  | nil (N : Network n State Input Output Internal Mem) : NetExec N [] N
  | cons {N N' N'' : Network n State Input Output Internal Mem}
      {i : Fin n} {a : Action Input Output Internal}
      {as : List (Fin n × Action Input Output Internal)} :
      NetStep N N' i a → NetExec N' as N'' → NetExec N ((i, a) :: as) N''

theorem NetExec.cons_inv {n : Nat} {State Input Output Internal Mem : Type u}
    {N N'' : Network n State Input Output Internal Mem}
    {i : Fin n} {a : Action Input Output Internal}
    {as : List (Fin n × Action Input Output Internal)} :
    NetExec N ((i, a) :: as) N'' →
    ∃ N', NetStep N N' i a ∧ NetExec N' as N'' := by
  intro h
  cases h with
  | cons hstep hexec =>
      exact ⟨_, hstep, hexec⟩

theorem NetExec.append {n : Nat} {State Input Output Internal Mem : Type u}
    {N N' N'' : Network n State Input Output Internal Mem}
    {as bs : List (Fin n × Action Input Output Internal)} :
    NetExec N as N' → NetExec N' bs N'' → NetExec N (as ++ bs) N'' := by
  intro h1 h2
  induction h1 with
  | nil N =>
      simpa using h2
  | cons hstep hexec ih =>
      exact NetExec.cons hstep (ih h2)

theorem NetExec.automata_eq {n : Nat} {State Input Output Internal Mem : Type u}
    {N N' : Network n State Input Output Internal Mem}
    {as : List (Fin n × Action Input Output Internal)} :
    NetExec N as N' → N.automata = N'.automata := by
  intro h
  induction h with
  | nil N =>
      rfl
  | cons hstep hexec ih =>
      rcases hstep with ⟨hauto, _hstep, _hstate, _hmem⟩
      exact hauto.trans ih

theorem NetExec.strong_induction {n : Nat} {State Input Output Internal Mem : Type u}
    (P : Network n State Input Output Internal Mem →
      List (Fin n × Action Input Output Internal) →
      Network n State Input Output Internal Mem → Prop)
    (h0 : ∀ N, P N [] N)
    (hcons :
      ∀ N i a as N',
        (∀ N1 as1 N2, as1.length < ((i, a) :: as).length →
          NetExec N1 as1 N2 → P N1 as1 N2) →
        NetExec N ((i, a) :: as) N' → P N ((i, a) :: as) N') :
    ∀ N as N', NetExec N as N' → P N as N' := by
  intro N as N' hexec
  refine (Nat.strong_induction_on
      (p := fun n =>
        ∀ N as N', as.length = n → NetExec N as N' → P N as N')
      as.length ?_) N as N' rfl hexec
  intro n ih N as N' hlen hexec
  cases as with
  | nil =>
      cases hexec with
      | nil N =>
          simpa using h0 N
  | cons ia as =>
      rcases ia with ⟨i, a⟩
      have hcons_exec : NetExec N ((i, a) :: as) N' := by
        simpa using hexec
      rcases NetExec.cons_inv (N := N) (N'' := N') (i := i) (a := a) (as := as) hcons_exec with
        ⟨N1, hstep, hexec'⟩
      have ih' :
          ∀ N1 as1 N2, as1.length < ((i, a) :: as).length →
            NetExec N1 as1 N2 → P N1 as1 N2 := by
        intro N1 as1 N2 hlt hexec1
        have hlt' : as1.length < n := by
          simpa [hlen] using hlt
        exact ih _ hlt' N1 as1 N2 rfl hexec1
      exact hcons N i a as N' ih' hcons_exec

-- Defines the Prop that a list of actions form a trace
def NetTrace {n : Nat} {State Input Output Internal Mem : Type u}
    (N : Network n State Input Output Internal Mem)
    (as : List (Fin n × Action Input Output Internal)) : Prop :=
  ∃ N', NetExec N as N'

theorem NetTrace.nil {n : Nat} {State Input Output Internal Mem : Type u}
    (N : Network n State Input Output Internal Mem) :
    NetTrace N [] := by
  exact ⟨N, NetExec.nil N⟩

theorem NetTrace.cons_inv {n : Nat} {State Input Output Internal Mem : Type u}
    {N : Network n State Input Output Internal Mem}
    {i : Fin n} {a : Action Input Output Internal}
    {as : List (Fin n × Action Input Output Internal)} :
    NetTrace N ((i, a) :: as) →
    ∃ N', NetStep N N' i a ∧ NetTrace N' as := by
  intro h
  rcases h with ⟨N'', hexec⟩
  rcases NetExec.cons_inv (N := N) (N'' := N'') (i := i) (a := a) (as := as) hexec with
    ⟨N', hstep, htail⟩
  exact ⟨N', hstep, ⟨N'', htail⟩⟩

theorem NetTrace.append {n : Nat} {State Input Output Internal Mem : Type u}
    {N : Network n State Input Output Internal Mem}
    {as bs : List (Fin n × Action Input Output Internal)} :
    NetTrace N as →
      (∀ N', NetExec N as N' → NetTrace N' bs) →
      NetTrace N (as ++ bs) := by
  intro h1 h2
  rcases h1 with ⟨N', hexec1⟩
  rcases h2 N' hexec1 with ⟨N'', hexec2⟩
  exact ⟨N'', NetExec.append hexec1 hexec2⟩

theorem NetTrace.automata_eq {n : Nat} {State Input Output Internal Mem : Type u}
    {N : Network n State Input Output Internal Mem}
    {as : List (Fin n × Action Input Output Internal)} :
    NetTrace N as → ∃ N', N'.automata = N.automata ∧ NetExec N as N' := by
  intro h
  rcases h with ⟨N', hexec⟩
  exact ⟨N', (NetExec.automata_eq hexec).symm, hexec⟩

coinductive NetExecInf {n : Nat} {State Input Output Internal Mem : Type u} :
    Network n State Input Output Internal Mem →
    Stream' (Fin n × Action Input Output Internal) → Prop
  | step {N N' : Network n State Input Output Internal Mem}
      {tr : Stream' (Fin n × Action Input Output Internal)} :
      NetStep N N' (Stream'.head tr).1 (Stream'.head tr).2 →
      NetExecInf N' (Stream'.tail tr) →
      NetExecInf N tr

def NetTraceInf {n : Nat} {State Input Output Internal Mem : Type u}
    (N : Network n State Input Output Internal Mem)
    (tr : Stream' (Fin n × Action Input Output Internal)) : Prop :=
  NetExecInf N tr

theorem NetTraceInf.cons_inv {n : Nat} {State Input Output Internal Mem : Type u}
    {N : Network n State Input Output Internal Mem}
    {tr : Stream' (Fin n × Action Input Output Internal)} :
    NetTraceInf N tr →
    ∃ N', NetStep N N' (Stream'.head tr).1 (Stream'.head tr).2 ∧
      NetTraceInf N' (Stream'.tail tr) := by
  intro h
  dsimp [NetTraceInf] at h
  cases h with
  | step hstep htail =>
      exact ⟨_, hstep, htail⟩

theorem NetTraceInf.append {n : Nat} {State Input Output Internal Mem : Type u}
    {N N' : Network n State Input Output Internal Mem}
    {as : List (Fin n × Action Input Output Internal)}
    {tr : Stream' (Fin n × Action Input Output Internal)} :
    NetExec N as N' → NetTraceInf N' tr →
    NetTraceInf N (Stream'.appendStream' as tr) := by
  intro hexec hinf
  induction hexec with
  | nil N =>
      simpa using hinf
  | cons hstep hexec ih =>
      rename_i N0 N1 N2 i a as
      refine NetExecInf.step (N := N0) (N' := N1) ?_ ?_
      · simpa [Stream'.appendStream'] using hstep
      · simpa [Stream'.appendStream'] using (ih hinf)

theorem NetTraceInf.automata_eq {n : Nat} {State Input Output Internal Mem : Type u}
    {N : Network n State Input Output Internal Mem}
    {tr : Stream' (Fin n × Action Input Output Internal)} :
    NetTraceInf N tr →
    ∃ N' : Network n State Input Output Internal Mem,
      N'.automata = N.automata ∧ NetTraceInf N' (Stream'.tail tr) := by
  intro h
  rcases NetTraceInf.cons_inv (N := N) (tr := tr) h with ⟨N', hstep, htail⟩
  rcases hstep with ⟨hauto, _hstep, _hstate, _hmem⟩
  exact ⟨N', hauto.symm, htail⟩

end Network

end Consensus
