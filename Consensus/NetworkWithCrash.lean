import Mathlib
import Consensus.Network

namespace Consensus

namespace Network

/-- Status of a node in a crash-fault model. -/
inductive NodeStatus where
  | alive
  | crashed

/-- A network configuration with per-node crash status and fixed input values. -/
structure NetConfig (n : Nat) (State Input Output Internal Mem Val : Type u) where
  net : Network n State Input Output Internal Mem
  status : Fin n → NodeStatus
  input : Fin n → Val

/-- A normal step by a live node; crash status is unchanged. -/
def LiveStep {n : Nat} {State Input Output Internal Mem Val : Type u}
    (C C' : NetConfig n State Input Output Internal Mem Val)
    (i : Fin n) (a : Action Input Output Internal) : Prop :=
  C.status i = NodeStatus.alive ∧
  C'.status = C.status ∧
  C'.input = C.input ∧
  NetStep C.net C'.net i a

/-- A crash step for a live node; the network state is unchanged. -/
def CrashStep {n : Nat} {State Input Output Internal Mem Val : Type u}
    (C C' : NetConfig n State Input Output Internal Mem Val)
    (i : Fin n) : Prop :=
  C.status i = NodeStatus.alive ∧
  C'.net = C.net ∧
  C'.input = C.input ∧
  C'.status = fun j => if _ : j = i then NodeStatus.crashed else C.status j

/-- One step of a configuration with crashes: either a live step or a crash step. -/
inductive NetStepWithCrash {n : Nat} {State Input Output Internal Mem Val : Type u} :
    NetConfig n State Input Output Internal Mem Val →
    (Fin n × Option (Action Input Output Internal)) →
    NetConfig n State Input Output Internal Mem Val → Prop
  | live {C C' : NetConfig n State Input Output Internal Mem Val}
      {i : Fin n} {a : Action Input Output Internal} :
      LiveStep C C' i a → NetStepWithCrash C (i, some a) C'
  | crash {C C' : NetConfig n State Input Output Internal Mem Val}
      {i : Fin n} :
      CrashStep C C' i → NetStepWithCrash C (i, none) C'

/-- Finite execution over crash-annotated steps. -/
inductive NetExecCrash {n : Nat} {State Input Output Internal Mem Val : Type u} :
    NetConfig n State Input Output Internal Mem Val →
    List (Fin n × Option (Action Input Output Internal)) →
    NetConfig n State Input Output Internal Mem Val → Prop
  | nil (C : NetConfig n State Input Output Internal Mem Val) : NetExecCrash C [] C
  | cons {C C' C'' : NetConfig n State Input Output Internal Mem Val}
      {i : Fin n} {a : Option (Action Input Output Internal)}
      {as : List (Fin n × Option (Action Input Output Internal))} :
      NetStepWithCrash C (i, a) C' →
      NetExecCrash C' as C'' →
      NetExecCrash C ((i, a) :: as) C''

/-- A crash-aware trace: there exists a finite execution producing it. -/
def NetTraceCrash {n : Nat} {State Input Output Internal Mem Val : Type u}
    (C : NetConfig n State Input Output Internal Mem Val)
    (as : List (Fin n × Option (Action Input Output Internal))) : Prop :=
  ∃ C', NetExecCrash C as C'

/-- Infinite execution over crash-annotated steps. -/
coinductive NetExecInfCrash {n : Nat} {State Input Output Internal Mem Val : Type u} :
    NetConfig n State Input Output Internal Mem Val →
    Stream' (Fin n × Option (Action Input Output Internal)) → Prop
  | step {C C' : NetConfig n State Input Output Internal Mem Val}
      {tr : Stream' (Fin n × Option (Action Input Output Internal))} :
      NetStepWithCrash C (Stream'.head tr) C' →
      NetExecInfCrash C' (Stream'.tail tr) →
      NetExecInfCrash C tr

/-- A crash-aware infinite trace: an infinite execution from the configuration. -/
def NetTraceInfCrash {n : Nat} {State Input Output Internal Mem Val : Type u}
    (C : NetConfig n State Input Output Internal Mem Val)
    (tr : Stream' (Fin n × Option (Action Input Output Internal))) : Prop :=
  NetExecInfCrash C tr

theorem NetExecCrash.cons_inv {n : Nat} {State Input Output Internal Mem Val : Type u}
    {C C'' : NetConfig n State Input Output Internal Mem Val}
    {i : Fin n} {a : Option (Action Input Output Internal)}
    {as : List (Fin n × Option (Action Input Output Internal))} :
    NetExecCrash C ((i, a) :: as) C'' →
    ∃ C', NetStepWithCrash C (i, a) C' ∧ NetExecCrash C' as C'' := by
  intro h
  cases h with
  | cons hstep hexec =>
      exact ⟨_, hstep, hexec⟩

theorem NetExecCrash.append {n : Nat} {State Input Output Internal Mem Val : Type u}
    {C C' C'' : NetConfig n State Input Output Internal Mem Val}
    {as bs : List (Fin n × Option (Action Input Output Internal))} :
    NetExecCrash C as C' → NetExecCrash C' bs C'' → NetExecCrash C (as ++ bs) C'' := by
  intro h1 h2
  induction h1 with
  | nil C =>
      simpa using h2
  | cons hstep hexec ih =>
      exact NetExecCrash.cons hstep (ih h2)

theorem NetExecCrash.automata_eq {n : Nat} {State Input Output Internal Mem Val : Type u}
    {C C' : NetConfig n State Input Output Internal Mem Val}
    {as : List (Fin n × Option (Action Input Output Internal))} :
    NetExecCrash C as C' → C.net.automata = C'.net.automata := by
  intro h
  induction h with
  | nil C =>
      rfl
  | cons hstep hexec ih =>
      rename_i C0 C1 C2 i a as
      have hauto : C0.net.automata = C1.net.automata := by
        cases hstep with
        | live h =>
            rcases h with ⟨_hstat, _hstat', _hinput, hstep'⟩
            rcases hstep' with ⟨hauto, _hstep, _hstate, _hmem⟩
            exact hauto
        | crash h =>
            rcases h with ⟨_hstat, hnet, _hinput, _hstat'⟩
            simp [hnet]
      exact hauto.trans ih

theorem NetExecCrash.strong_induction {n : Nat} {State Input Output Internal Mem Val : Type u}
    (P : NetConfig n State Input Output Internal Mem Val →
      List (Fin n × Option (Action Input Output Internal)) →
      NetConfig n State Input Output Internal Mem Val → Prop)
    (h0 : ∀ C, P C [] C)
    (hcons :
      ∀ C i a as C',
        (∀ C1 as1 C2, as1.length < ((i, a) :: as).length →
          NetExecCrash C1 as1 C2 → P C1 as1 C2) →
        NetExecCrash C ((i, a) :: as) C' → P C ((i, a) :: as) C') :
    ∀ C as C', NetExecCrash C as C' → P C as C' := by
  intro C as C' hexec
  refine (Nat.strong_induction_on
      (p := fun n =>
        ∀ C as C', as.length = n → NetExecCrash C as C' → P C as C')
      as.length ?_) C as C' rfl hexec
  intro n ih C as C' hlen hexec
  cases as with
  | nil =>
      cases hexec with
      | nil C =>
          simpa using h0 C
  | cons ia as =>
      rcases ia with ⟨i, a⟩
      have hcons_exec : NetExecCrash C ((i, a) :: as) C' := by
        simpa using hexec
      rcases NetExecCrash.cons_inv (C := C) (C'' := C') (i := i) (a := a) (as := as) hcons_exec with
        ⟨C1, hstep, hexec'⟩
      have ih' :
          ∀ C1 as1 C2, as1.length < ((i, a) :: as).length →
            NetExecCrash C1 as1 C2 → P C1 as1 C2 := by
        intro C1 as1 C2 hlt hexec1
        have hlt' : as1.length < n := by
          simpa [hlen] using hlt
        exact ih _ hlt' C1 as1 C2 rfl hexec1
      exact hcons C i a as C' ih' hcons_exec

theorem NetTraceCrash.nil {n : Nat} {State Input Output Internal Mem Val : Type u}
    (C : NetConfig n State Input Output Internal Mem Val) :
    NetTraceCrash C [] := by
  exact ⟨C, NetExecCrash.nil C⟩

theorem NetTraceCrash.cons_inv {n : Nat} {State Input Output Internal Mem Val : Type u}
    {C : NetConfig n State Input Output Internal Mem Val}
    {i : Fin n} {a : Option (Action Input Output Internal)}
    {as : List (Fin n × Option (Action Input Output Internal))} :
    NetTraceCrash C ((i, a) :: as) →
    ∃ C', NetStepWithCrash C (i, a) C' ∧ NetTraceCrash C' as := by
  intro h
  rcases h with ⟨C'', hexec⟩
  rcases NetExecCrash.cons_inv (C := C) (C'' := C'') (i := i) (a := a) (as := as) hexec with
    ⟨C', hstep, htail⟩
  exact ⟨C', hstep, ⟨C'', htail⟩⟩

theorem NetTraceCrash.append {n : Nat} {State Input Output Internal Mem Val : Type u}
    {C : NetConfig n State Input Output Internal Mem Val}
    {as bs : List (Fin n × Option (Action Input Output Internal))} :
    NetTraceCrash C as →
      (∀ C', NetExecCrash C as C' → NetTraceCrash C' bs) →
      NetTraceCrash C (as ++ bs) := by
  intro h1 h2
  rcases h1 with ⟨C', hexec1⟩
  rcases h2 C' hexec1 with ⟨C'', hexec2⟩
  exact ⟨C'', NetExecCrash.append hexec1 hexec2⟩

theorem NetTraceCrash.automata_eq {n : Nat} {State Input Output Internal Mem Val : Type u}
    {C : NetConfig n State Input Output Internal Mem Val}
    {as : List (Fin n × Option (Action Input Output Internal))} :
    NetTraceCrash C as →
    ∃ C', C'.net.automata = C.net.automata ∧ NetExecCrash C as C' := by
  intro h
  rcases h with ⟨C', hexec⟩
  exact ⟨C', (NetExecCrash.automata_eq hexec).symm, hexec⟩

theorem NetTraceInfCrash.cons_inv {n : Nat} {State Input Output Internal Mem Val : Type u}
    {C : NetConfig n State Input Output Internal Mem Val}
    {tr : Stream' (Fin n × Option (Action Input Output Internal))} :
    NetTraceInfCrash C tr →
    ∃ C', NetStepWithCrash C (Stream'.head tr) C' ∧
      NetTraceInfCrash C' (Stream'.tail tr) := by
  intro h
  dsimp [NetTraceInfCrash] at h
  cases h with
  | step hstep htail =>
      exact ⟨_, hstep, htail⟩

theorem NetTraceInfCrash.append {n : Nat} {State Input Output Internal Mem Val : Type u}
    {C C' : NetConfig n State Input Output Internal Mem Val}
    {as : List (Fin n × Option (Action Input Output Internal))}
    {tr : Stream' (Fin n × Option (Action Input Output Internal))} :
    NetExecCrash C as C' → NetTraceInfCrash C' tr →
    NetTraceInfCrash C (Stream'.appendStream' as tr) := by
  intro hexec hinf
  induction hexec with
  | nil C =>
      simpa using hinf
  | cons hstep hexec ih =>
      rename_i C0 C1 C2 i a as
      refine NetExecInfCrash.step (C := C0) (C' := C1) ?_ ?_
      · simpa [Stream'.appendStream'] using hstep
      · simpa [Stream'.appendStream'] using (ih hinf)

theorem NetTraceInfCrash.automata_eq {n : Nat} {State Input Output Internal Mem Val : Type u}
    {C : NetConfig n State Input Output Internal Mem Val}
    {tr : Stream' (Fin n × Option (Action Input Output Internal))} :
    NetTraceInfCrash C tr →
    ∃ C' : NetConfig n State Input Output Internal Mem Val,
      C'.net.automata = C.net.automata ∧ NetTraceInfCrash C' (Stream'.tail tr) := by
  intro h
  rcases NetTraceInfCrash.cons_inv (C := C) (tr := tr) h with ⟨C', hstep, htail⟩
  have hauto : C.net.automata = C'.net.automata := by
    cases hlabel : Stream'.head tr with
    | mk i oa =>
        have hstep' : NetStepWithCrash C (i, oa) C' := by
          simpa [hlabel] using hstep
        cases hstep' with
        | live h =>
            rcases h with ⟨_hstat, _hstat', _hinput, hstep''⟩
            rcases hstep'' with ⟨hauto, _hstep, _hstate, _hmem⟩
            exact hauto
        | crash h =>
            rcases h with ⟨_hstat, hnet, _hinput, _hstat'⟩
            simp [hnet]
  exact ⟨C', hauto.symm, htail⟩

end Network

end Consensus
