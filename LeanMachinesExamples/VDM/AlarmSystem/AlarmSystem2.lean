
import LeanMachines.Refinement.Strong.Basic
import LeanMachines.Refinement.Strong.Abstract
import LeanMachines.Refinement.Strong.Concrete

import LeanMachinesExamples.VDM.AlarmSystem.AlarmSystem1

/-!

## Second refinement: on-duty schedule

In this second refinement, the alarms are (at last) introduced.

-/

namespace AlarmSystem

/-- The representation of an alarm.
For the sake of simplicity, we did not specify any text
 accompanying the alarm. -/
structure Alarm where
  /-- The period when the alarm was raised. -/
  period : Period
  /-- The expert qualification required to handle the alarm. -/
  quali : Qualification
  deriving DecidableEq

/-- The state representation of the second alarm system refinement.
This is again a superposition situation. -/
structure ASys2 (ctx : ASys1.Context) extends ASys1 ctx where
  /-- the raised alarms. Note that a list is used as a convenience,
  but the ordering of alarms is arbitrary. Note that two alarms
  for the same period with the same qualification requirement
  could be raised, hence we need a multiset and a list fits such
  requirement.  -/
  alarms : List Alarm

/-- Invariant: the abstract invariant holds (superposition). -/
@[simp]
def ASys2.invariant₁ (asys : ASys2 ctx) := Machine.invariant asys.toASys1

/-- Invariant: a raised alarm has to be handled, thus an adequately
qualified expert must be on-duty in the schedule. -/
def ASys2.invariant₂ (asys : ASys2 ctx) :=
  ∀ alarm ∈ asys.alarms, ∃ exp ∈ asys.schedule alarm.period, exp.quali = alarm.quali

/-- The machine specification of the second alarm system refinement. -/
instance: Machine ASys1.Context (ASys2 ctx) where
  context := ctx
  invariant asys := ASys2.invariant₁ asys ∧ ASys2.invariant₂ asys
  reset := { toASys1 := Machine.reset
             alarms := [] }

/-- The specification of correct strong functional refinement. -/
instance: SRefinement  (ASys1 ctx) (ASys2 ctx) where
  lift asys := asys.toASys1
  lift_safe asys := by
    simp [Machine.invariant] ; intros ; simp [*]

  unlift asys2 asys1' := { toASys1 := asys1'
                           alarms := asys2.alarms }

  lift_unlift asys2 asys1' := by simp
  lu_reset asys1' := by simp

namespace ASys2

/-- Initialization event: empty alarm system (no expert, no scheduled period, no alarm).
Refinement of `Asys1.Init`.-/
def Init : InitEvent (ASys2 ctx) Unit Unit := newInitEvent'' {
  init := Machine.reset
  safety := by
    intro H ; clear H
    simp [Machine.reset, Machine.invariant
         , ASys0.invariant₁, ASys0.invariant₂, ASys1.invariant₂, ASys1.invariant₃
         , ASys2.invariant₂]
}

theorem superposition (asys : ASys2 ctx):
  Machine.invariant asys.toASys1
  → invariant₂ asys
  → Machine.invariant asys :=
by
  cases asys
  case mk _toASys1 _alarms =>
    simp
    intros Hainv Hinv₅
    simp [Machine.invariant] at *
    simp [*]

/-- Event: Adding an expert, a refinement of `ASys1.AddExpert`.
This reuses the abstract event. -/
def AddExpert : ConvergentREvent Nat (ASys1 ctx) (ASys2 ctx) Expert Unit :=
  newAbstractConvergentSREvent' ASys1.AddExpert.toConvergentEvent {
    step_inv := fun asys exp => by
      simp [FRefinement.lift, SRefinement.unlift]
      intros Hinv Hgrd
      have Hainv : Machine.invariant asys.toASys1 := by
        exact Refinement.refine_safe asys.toASys1 asys Hinv rfl
      have HSafe := ASys1.AddExpert.po.safety asys.toASys1 exp Hainv Hgrd
      apply superposition
      · exact HSafe
      -- next
      obtain ⟨_, Hinv₂⟩ := Hinv
      simp [ASys2.invariant₂] at *
      simp [ASys1.AddExpert, SRefinement.unlift]
      intros alarm Halarm
      exact Hinv₂ alarm Halarm
}

/-- Event: expert assignment, a refinement of `ASys1.AssignExpert`.
This reuses the abstract event (and it is not *that* trivial that
 the concrete alarm constraint is preserved). -/
def AssignExpert : OrdinaryREvent (ASys1 ctx) (ASys2 ctx) (Period × Expert) Unit :=
  newAbstractSREvent' ASys1.AssignExpert.toOrdinaryEvent {
    step_inv := fun asys (p, e) => by
      simp [FRefinement.lift, SRefinement.unlift]
      intros Hinv Hgrd
      have Hainv : Machine.invariant asys.toASys1 := by
        exact Refinement.refine_safe asys.toASys1 asys Hinv rfl
      have HSafe := ASys1.AssignExpert.po.safety asys.toASys1 (p, e) Hainv Hgrd
      apply superposition
      · exact HSafe
      -- next
      obtain ⟨_, Hinv₂⟩ := Hinv
      simp [ASys2.invariant₂] at *
      simp [ASys1.AssignExpert]
      intros alarm Halarm
      have Hinv₂' := Hinv₂ alarm Halarm
      split
      case _ Heq =>
        rw [Heq] at Hinv₂'
        obtain ⟨e', ⟨Hinv₂', Hinv₂''⟩⟩ := Hinv₂'
        exists e'
        constructor
        · exact Finset.mem_union_left {e} Hinv₂'
        -- next
        assumption
      case _ Hneq =>
        assumption
  }

/-- Concrete Event: raising an alarm. -/
def RaiseAlarm : OrdinaryRDetEvent (ASys1 ctx) (ASys2 ctx) Alarm Unit :=
  newConcreteSREvent' {
    guard := fun asys alarm =>
               ∃ exp ∈ asys.schedule alarm.period, exp.quali = alarm.quali
    action := fun asys alarm => { asys with alarms := alarm :: asys.alarms }

    safety := fun asys alarm => by
      intro Hinv
      obtain ⟨⟨⟨Haainv₁, Haainv₂⟩, Hainv₂, Hainv₃⟩, Hinv₂⟩ := Hinv
      simp
      intros exp Hgrd₁ Hgrd₂
      simp [Machine.invariant]
      simp [*, ASys2.invariant₂]
      constructor
      · exists exp
      intros alarm' Halarm'
      exact Hinv₂ alarm' Halarm'

    simulation := fun asys alarm => by
      intros ; simp [FRefinement.lift]

  }
