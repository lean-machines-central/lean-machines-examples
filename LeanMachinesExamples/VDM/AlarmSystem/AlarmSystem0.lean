import Mathlib.Tactic
import Mathlib.Data.Finset.Basic

import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent

/-!

# VDM AlarmSystem specification

This example is inspired by the VDM specificatio of an alarm system
given in the book:

    Modelling Systems: Practical Tools and Techniques for Software Development: 2nd Edition
    by John Fitzgerald and Peter Gorm Larsen
    (Cambridge University Press, 2nd Edition, 2009 ISBN 0 521 62348 0)

We adopt here a very "liberal" interpretation in that the example is largely
reintrepreted. First, the VDM example does not involve refinement -- which is
the main purpose of LeanMachines. Moreover, it is an example of a *stateless*
specification. Our reinterpretation involves an abstract machine and two refinement
 steps.

  - the abstract machine only specifies the management of *experts*
    (cf. the original specification)

  - the first refinement introduces the *schedule* for the on-call duty periods for experts.

  - the second refinement finally introduces the alarms and alarms-handling functionalities
    of the system.

We also of course introduce an explicit state management for the alarm system, making
it a *stateful* formalization.

We think that this example fits quite nicely the LeanMachines framework principles, thanks to its
mostly functional nature.

-/

/-!

## Abstract machine

-/

namespace AlarmSystem

/-- Qualification of experts.-/
inductive Qualification where
| Elec | Mech | Bio | Chem
  deriving Repr, DecidableEq

/-- Identification of experts.

**Remark**: while in VDM the `token` type is often use to
manipulate abstract identifiers and more generally
abstract sets, it is in general best to be more
concrete in Lean4, which is before all a functional
programming language
(of course, abstract sets/types are defineable, but then
testing or "playing" with the specifications is impossible). -/
abbrev ExpertId := Nat

/-- The representations of experts in the alarm system. -/
structure Expert where
  /-- The (unique) identifier of the expert. -/
  id : ExpertId
  /-- The qualification of the expert.
  Note that in the original specification an expert can have
  multiple (a list of) qualifications. Here we simplify the
  model somehow (since our objective is not to discuss lists,
  as in the original specification.)-/
  quali : Qualification
  deriving Repr, DecidableEq   -- experts must be comparable for equality

/-- The context of the alarm system. -/
structure ASys0.Context where
  /-- Parameter: the (static) maximum number of experts registered in the system.-/
  maxExperts : Nat
  maxExperts_prop : maxExperts > 0
  deriving Repr

/-- State representation of the abstract alarm system. -/
structure ASys0 (ctx : ASys0.Context) where
  /-- The set of experts currently in the (for now, unspecified) on-duty schedule. -/
  experts : Finset Expert

/-- Invariant: the number of experts satisfies is below the limit. -/
def ASys0.invariant₁ (asys : ASys0 ctx) : Prop :=
  asys.experts.card ≤ ctx.maxExperts

/-- Invariant: distinct experts have distinct ids. -/
def ASys0.invariant₂ (asys : ASys0 ctx) : Prop :=
  ∀ exp₁ ∈ asys.experts, ∀ exp₂ ∈ asys.experts,
    exp₁ ≠ exp₂ → exp₁.id ≠ exp₂.id

/-- The reset state of the abstract system: no expert on-duty. -/
@[simp]
def ASys0.reset : ASys0 ctx := { experts := ∅ }

/-- The machine specification of the abstract alarm system. -/
instance: Machine ASys0.Context (ASys0 ctx) where
  context := ctx
  invariant asys := ASys0.invariant₁ asys ∧ ASys0.invariant₂ asys
  reset := ASys0.reset

namespace ASys0

/-- Initialization event: empty alarm system (no expert on duty). -/
def Init : InitEvent (ASys0 ctx) Unit Unit := newInitEvent'' {
  init := ASys0.reset
  safety := by
    intro H ; clear H
    simp [Machine.invariant, ASys0.invariant₁, ASys0.invariant₂]
}

/-- Event: Adding the specified expert in the on-duty schedule.
Note: the event is convergent. -/
def AddExpert : ConvergentEvent Nat (ASys0 ctx) Expert Unit := newConvergentEvent' {
  guard := fun asys exp => exp ∉ asys.experts ∧ asys.experts.card < ctx.maxExperts ∧ ∀ exp' ∈ asys.experts, exp'.id ≠ exp.id
  action := fun asys exp => { experts := asys.experts ∪ {exp} }

  safety := fun asys exp => by
    simp [Machine.invariant]
    intros _ Hinv₂ _ Hgrd₂ Hgrd₃
    constructor
    case left =>
      simp [ASys0.invariant₁] at *
      have Hcard := Finset.card_union_le asys.experts {exp}
      simp at Hcard
      exact Nat.le_trans Hcard Hgrd₂
    case right =>
      simp [ASys0.invariant₂] at *
      intros exp1 Hexp₁ exp₂ Hexp₂ Hneq
      cases Hexp₁
      case inl Hexp₁ =>
        cases Hexp₂
        case inl Hexp₂ =>
          exact Hinv₂ exp1 Hexp₁ exp₂ Hexp₂ Hneq
        case inr Hexp₂ =>
          rw [Hexp₂] at *
          exact Hgrd₃ exp1 Hexp₁
      case inr Hexp₁ =>
        cases Hexp₂
        case inl Hexp₂ =>
          rw [Hexp₁] at *
          exact fun a => Hgrd₃ exp₂ Hexp₂ (id (Eq.symm a))
        case inr Hexp₂ =>
          rw [Hexp₁, Hexp₂] at Hneq
          contradiction

  variant := fun (asys : ASys0 ctx) => ctx.maxExperts - asys.experts.card

  convergence := fun asys exp => by
    simp [Machine.invariant]
    intros _ _ Hgrd₁ Hgrd₂ Hgrd₃
    refine Nat.sub_lt_sub_left Hgrd₂ ?_ -- apply?
    refine Finset.card_lt_card ?h -- apply?
    refine Finset.ssubset_iff_subset_ne.mpr ?h.a -- apply?
    constructor
    · exact Finset.subset_union_left
    · intro Hcontra
      rw [Hcontra] at Hgrd₁
      have Hin: exp ∈ asys.experts ∪ {exp} := by
        refine Finset.mem_union_right asys.experts ?hh -- apply?
        exact Finset.mem_singleton.mpr rfl -- apply?
      contradiction
}

end ASys0

end AlarmSystem
