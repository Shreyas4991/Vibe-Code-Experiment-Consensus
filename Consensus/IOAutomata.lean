import Mathlib

namespace Consensus

inductive Action (Input Output Internal : Type u) where
  | inp : Input → Action Input Output Internal
  | out : Output → Action Input Output Internal
  | internal : Internal → Action Input Output Internal

structure IOAutomaton (State Input Output Internal : Type u) where
  start : Set State
  step : State → Action Input Output Internal → State → Prop

def inputEnabled {State Input Output Internal : Type u}
    (A : IOAutomaton State Input Output Internal) : Prop :=
  ∀ s i, ∃ s', A.step s (Action.inp i) s'

def deterministic {State Input Output Internal : Type u}
    (A : IOAutomaton State Input Output Internal) : Prop :=
  ∀ s a s1 s2, A.step s a s1 → A.step s a s2 → s1 = s2

def outputDeterministic {State Input Output Internal : Type u}
    (A : IOAutomaton State Input Output Internal) : Prop :=
  ∀ s o s1 s2, A.step s (Action.out o) s1 → A.step s (Action.out o) s2 → s1 = s2

def internalDeterministic {State Input Output Internal : Type u}
    (A : IOAutomaton State Input Output Internal) : Prop :=
  ∀ s i s1 s2, A.step s (Action.internal i) s1 → A.step s (Action.internal i) s2 → s1 = s2

inductive Exec {State Input Output Internal : Type u}
    (A : IOAutomaton State Input Output Internal) :
    State → List (Action Input Output Internal) → State → Prop
  | nil (s : State) : Exec A s [] s
  | cons {s s' t : State} {a : Action Input Output Internal}
      {as : List (Action Input Output Internal)} :
      A.step s a s' → Exec A s' as t → Exec A s (a :: as) t

theorem Exec.cons_inv {State Input Output Internal : Type u}
    {A : IOAutomaton State Input Output Internal} {s t : State}
    {a : Action Input Output Internal} {as : List (Action Input Output Internal)} :
    Exec A s (a :: as) t →
    ∃ s', A.step s a s' ∧ Exec A s' as t := by
  intro h
  cases h with
  | cons hstep hexec =>
      exact ⟨_, hstep, hexec⟩

theorem Exec.append {State Input Output Internal : Type u}
    {A : IOAutomaton State Input Output Internal} {s t u : State}
    {as bs : List (Action Input Output Internal)} :
    Exec A s as t → Exec A t bs u → Exec A s (as ++ bs) u := by
  intro h1 h2
  induction h1 with
  | nil s =>
      simpa using h2
  | cons hstep _hexec ih =>
      exact Exec.cons hstep (ih h2)

theorem Exec.exists_states {State Input Output Internal : Type u}
    {A : IOAutomaton State Input Output Internal} {s t : State}
    {as : List (Action Input Output Internal)} :
    Exec A s as t →
    ∃ ss : List State,
      ss.length = as.length + 1 ∧ ss.head? = some s ∧ ss.getLast? = some t := by
  intro h
  induction h with
  | nil s =>
      refine ⟨[s], ?_, ?_, ?_⟩ <;> simp
  | cons hstep hexec ih =>
      rename_i s s' t a as
      rcases ih with ⟨ss, hlen, hhead, hlast⟩
      refine ⟨s :: ss, ?_, ?_, ?_⟩
      · simp [hlen]
      · simp [List.head?_cons]
      · simp [List.getLast?_cons, hlast]

theorem Exec.strong_induction {State Input Output Internal : Type u}
    {A : IOAutomaton State Input Output Internal}
    (P : State → List (Action Input Output Internal) → State → Prop)
    (h0 : ∀ s, P s [] s)
    (hcons :
      ∀ s a as t,
        (∀ s' as' t', as'.length < (a :: as).length →
          Exec A s' as' t' → P s' as' t') →
        Exec A s (a :: as) t → P s (a :: as) t) :
    ∀ s as t, Exec A s as t → P s as t := by
  intro s as t hexec
  refine (Nat.strong_induction_on
      (p := fun n => ∀ s as t, as.length = n → Exec A s as t → P s as t)
      as.length ?_) s as t rfl hexec
  intro n ih s as t hlen hexec
  cases as with
  | nil =>
      cases hexec with
      | nil s =>
          simpa using h0 s
  | cons a as =>
      have hcons_exec : Exec A s (a :: as) t := by
        simpa using hexec
      rcases Exec.cons_inv (s := s) (t := t) (a := a) (as := as) hcons_exec with
        ⟨s', hstep, hexec'⟩
      have ih' :
          ∀ s' as' t', as'.length < (a :: as).length →
            Exec A s' as' t' → P s' as' t' := by
        intro s' as' t' hlt hexec''
        have hlt' : as'.length < n := by
          simpa [hlen] using hlt
        exact ih _ hlt' s' as' t' rfl hexec''
      exact hcons s a as t ih' hcons_exec

def Trace {State Input Output Internal : Type u}
    (A : IOAutomaton State Input Output Internal)
    (as : List (Action Input Output Internal)) : Prop :=
  ∃ s t, s ∈ A.start ∧ Exec A s as t

coinductive ExecInf {State Input Output Internal : Type u}
    (A : IOAutomaton State Input Output Internal) :
    State → Stream' (Action Input Output Internal) → Prop
  | step {s s' : State} {as : Stream' (Action Input Output Internal)} :
      A.step s (Stream'.head as) s' →
      ExecInf A s' (Stream'.tail as) →
      ExecInf A s as

def TraceInf {State Input Output Internal : Type u}
    (A : IOAutomaton State Input Output Internal)
    (as : Stream' (Action Input Output Internal)) : Prop :=
  ∃ s, s ∈ A.start ∧ ExecInf A s as

theorem ExecInf.unfold {State Input Output Internal : Type u}
    {A : IOAutomaton State Input Output Internal} {s : State}
    {as : Stream' (Action Input Output Internal)} :
    ExecInf A s as →
    ∃ s', A.step s (Stream'.head as) s' ∧ ExecInf A s' (Stream'.tail as) := by
  intro h
  cases h with
  | step hstep hexec =>
      exact ⟨_, hstep, hexec⟩

theorem TraceInf.unfold {State Input Output Internal : Type u}
    {A : IOAutomaton State Input Output Internal}
    {as : Stream' (Action Input Output Internal)} :
    TraceInf A as →
    ∃ s s', s ∈ A.start ∧ A.step s (Stream'.head as) s' ∧
      ExecInf A s' (Stream'.tail as) := by
  intro h
  rcases h with ⟨s, hstart, hexec⟩
  rcases ExecInf.unfold hexec with ⟨s', hstep, htail⟩
  exact ⟨s, s', hstart, hstep, htail⟩

theorem TraceInf.exists_start {State Input Output Internal : Type u}
    {A : IOAutomaton State Input Output Internal}
    {as : Stream' (Action Input Output Internal)} :
    TraceInf A as → ∃ s, s ∈ A.start := by
  intro h
  rcases h with ⟨s, hstart, _⟩
  exact ⟨s, hstart⟩

theorem ExecInf.tail_exists {State Input Output Internal : Type u}
    {A : IOAutomaton State Input Output Internal} {s : State}
    {as : Stream' (Action Input Output Internal)} :
    ExecInf A s as → ∃ s', ExecInf A s' (Stream'.tail as) := by
  intro h
  rcases ExecInf.unfold h with ⟨s', _hstep, htail⟩
  exact ⟨s', htail⟩

theorem TraceInf.tail_exists {State Input Output Internal : Type u}
    {A : IOAutomaton State Input Output Internal}
    {as : Stream' (Action Input Output Internal)} :
    TraceInf A as → ∃ s, ExecInf A s (Stream'.tail as) := by
  intro h
  rcases h with ⟨s, _hstart, hexec⟩
  exact ExecInf.tail_exists hexec

end Consensus
