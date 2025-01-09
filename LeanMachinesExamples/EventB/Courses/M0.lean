import Mathlib.Tactic

import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent
import LeanMachines.NonDet.Ordinary

import LeanMachinesExamples.EventB.Courses.Prelude

/-!

# Event-B tutorial specification

This example is a LeanMachines version of the specification
described in the book chapter :

   An Introduction to the Event-B Modelling Method
   by Thai Son Hoang

The original publication is available at http://www.springer.com/computer/swe/book/978-3-642-33169-5
In "Industrial Deployment of System Engineering Methods"  © Springer-Verlag

This is, at the technical level, a rather non-trivial example especially
for the LeanMachines framework because it is of a mostly relational and
non-detersministic nature (while LeanMachines favors functional and deterministic models,
when suitable) and also
because the tutorial shows several aspects of Event-B.
Also, it introduces a rather non-trivial example of data-refinement
between the first and second refinement.

We adopt here a relatively liberal interpretation of the original model
since the example is described rather informally in the original document,
 and also because the LeanMachines framework is *not* an Event-B implementation
 *per se*.  However, the state representation of the abstract and concrete
 machines are quite faithful to the original.

Informally, the specification is about a course management system in which,
roughtly, attendants can register to courses.

-/

/-!

## Abstract machine

In the abstract machine, only open/available courses are considered.

-/

namespace CoursesSpec

/-- The main context of the specification. -/
structure M0.Context where
  /-- Parameter: The (static) set of available courses. -/
  availableCourses : Finset Course
  /-- Parameter: The maximum number of courses currently opened for registration. -/
  maxOpenedCourses : Nat
  maxCourses_prop₁ : maxOpenedCourses > 0
  maxCourses_prop₂: maxOpenedCourses ≤ availableCourses.card

/-- The state representation of the abstract Courses machine-/
structure M0 (ctx : M0.Context) where
  /-- The set of courses currently opened for registration. -/
  openedCourses : Finset Course

/-- Invariant: the opened courses are available. -/
def M0.invariant₁ (m : M0 ctx) :=
  m.openedCourses ⊆ ctx.availableCourses

/-- Invariant: the number of opened courses satisfies the upper bound. -/
def M0.invariant₂ (m : M0 ctx)  :=
  m.openedCourses.card ≤  ctx.maxOpenedCourses

/-- The reset (pre-init) state of the system. -/
@[simp]
def M0.reset (ctx : M0.Context) : M0 ctx := {openedCourses := ∅}

/-- Specification of the abstract Courses machine. -/
instance: Machine M0.Context (M0 ctx) where
  context := ctx
  invariant m := M0.invariant₁ m ∧ M0.invariant₂ m
  reset := M0.reset ctx

namespace M0

/-!

## Events

In this example, given its non-trivial nature, we slightly change the way
events are constructed. First, we make a certain number of definitions and
theorems that corresponds to the main ingredients of the event:  guard, action and proof obligations.
This way, event specifications can be made gradually before empacking them within
 an event specification structure. This is largely thanks to the very "shallow" nature
 of the LeanMachines library.

Note, also, that proof olibgations can be "postponed" by using the `sorry` tactic hence
gradual *and* partial specifications are possible.

-/

/-!
### Initialization event
-/

namespace Init

@[simp]
def init : M0 ctx := {openedCourses := ∅}

theorem PO_safety₁:
  @invariant₁ ctx init :=
by
  simp [invariant₁]

theorem PO_safety₂:
  @invariant₂ ctx init :=
by
  simp [invariant₂]

end Init

/-- Initialization event: empty course system. -/
def Init : InitEvent (M0 ctx) Unit Unit := newInitEvent'' {
  init _ := Init.init
  safety := by
    simp [Machine.invariant, M0.invariant₁, M0.invariant₂, Init.PO_safety₁, Init.PO_safety₂]
}

/-!
## Event: opening courses

This event specification explains the opening of (a set of) courses
 for registration.

-/

namespace OpenCourses

/-! First, the guard specification. -/

/-- The guard specification of the `M0.OpenCourses` event:
 the maximum number of courses is not yet reached. -/
@[simp]
def guard (m : M0 ctx) := m.openedCourses.card ≠ ctx.maxOpenedCourses

-- a useful property for POs
theorem guard_lemma (m : M0 ctx):
  invariant₁ m → invariant₂ m
  → guard m
  → m.openedCourses.card ≠ ctx.availableCourses.card :=
by
  simp [invariant₁, invariant₂]
  intros Hinv₁ Hinv₂ Hgrd
  have Hctx₂ := ctx.maxCourses_prop₂
  have H₁ := Finset.card_le_card Hinv₁
  intro Hcontra
  simp [Hcontra] at * ; clear H₁ Hcontra
  have Hcontra: Finset.card ctx.availableCourses = ctx.maxOpenedCourses := by
    apply le_antisymm <;> assumption
  contradiction

/-- The effect of the `M0.OpenCourses` event:
  there is a (non-specified) non-empty subset of available courses the
  will be opened when applying the event.

**Remark**: Since the event is non-deterministic, what is described
is the (relational) **effect** is has on the machine's state.
Put in other terms, this describes the *properties* of the
event wrt. the state. -/
@[simp]
def effect (m m' : M0 ctx) : Prop :=
  ∃ cs : Finset Course, cs ⊆ ctx.availableCourses
    ∧ cs ≠ ∅
    ∧ m'.openedCourses = m.openedCourses ∪ cs
    ∧ m'.openedCourses.card ≤ ctx.maxOpenedCourses

/-! Proof obligations (as lean4 theorems): -/

-- PO: safety (part 1)
theorem PO_safety₁ (m : M0 ctx):
  invariant₁ m
  → ∀m', effect m m' → invariant₁ m' :=
by
  simp [invariant₁, invariant₂]
  intros Hinv₁ m' cs Hact₁ _ Hact₃ _
  simp [Hact₃]
  exact Finset.union_subset Hinv₁ Hact₁

-- PO: safety (part 2)
theorem PO_safety₂ (m : M0 ctx):
  invariant₂ m → guard m
  → ∀m', effect m m' → invariant₂ m' :=
by
  simp [invariant₂]

-- a lemma useful for feasibility
theorem M0.Context_available_courses_Nonempty (ctx : M0.Context):
  ctx.availableCourses ≠ ∅ :=
by
  have H₁ := ctx.maxCourses_prop₁
  have H₂ := ctx.maxCourses_prop₂
  intro Hcontra
  have Hcontra' : ctx.availableCourses.card = 0 := by exact Finset.card_eq_zero.mpr Hcontra
  linarith

-- PO: feasibility
theorem PO_Feasibility (m : M0 ctx):
  invariant₂ m → guard m
  → ∃ m', effect m m' :=
by
  simp [invariant₁, invariant₂]
  intros Hinv₂ Hgrd
  have Hctx₁ := ctx.maxCourses_prop₁
  have Hex: ∃ c, c ∈ ctx.availableCourses := by
    apply Finset_nonempty_ex
    apply M0.Context_available_courses_Nonempty
  cases Hex
  case intro c Hc =>
    exists { openedCourses := m.openedCourses ∪ {c}}
    exists {c}
    constructor
    · simp [Hc]
    · constructor
      · exact Finset.singleton_ne_empty c
      constructor
      · simp
      · have H₁ : Finset.card (m.openedCourses ∪ {c}) ≤ m.openedCourses.card + Finset.card {c} := by
          exact Finset.card_union_le m.openedCourses {c}
        simp at H₁
        have H₂: Finset.card m.openedCourses + 1 ≤ ctx.maxOpenedCourses := by
          apply Nat.add_le_of_le_sub
          · apply Hctx₁
          · apply Nat.le_pred_of_lt
            · exact Nat.lt_of_le_of_ne Hinv₂ Hgrd
        exact Nat.le_trans H₁ H₂

end OpenCourses

/-- Event: opening a new (available, unspecified) set of courses. -/
def OpenCourses : OrdinaryNDEvent (M0 ctx) Unit Unit :=
newNDEvent'' {
  guard := OpenCourses.guard
  effect m _ := OpenCourses.effect m
  safety := fun m => by
    simp [Machine.invariant, -OpenCourses.guard, -OpenCourses.effect]
    intros Hinv₁ Hinv₂ Hgrd m' Hact
    constructor
    · apply OpenCourses.PO_safety₁ <;> assumption
    · apply OpenCourses.PO_safety₂ <;> assumption
  feasibility := fun m => by
    simp [Machine.invariant]
    intros
    apply OpenCourses.PO_Feasibility <;> assumption
}

/-!
## Event: closing courses

This event describe the (functional, deterministic) closing of
a (specified) set of opened courses.

-/

namespace CloseCourses

/-- Guard of event `M0.CloseCourses`:
  Each course in the non-empty set `cs` of courses to close is opened. -/
@[simp]
def guard (m : M0 ctx) (cs : Finset Course) :=
  cs ⊆ m.openedCourses ∧ cs ≠ ∅

/-- Action of event `M0.CloseCourses`:
  The closed courses are removed from the set of opened ones. -/
@[simp]
def action (m : M0 ctx) (cs : Finset Course) : M0 ctx :=
  { openedCourses := m.openedCourses \ cs}

/-!  Proof obligations. -/

theorem PO_safety₁ (m : M0 ctx) (cs : Finset Course):
  invariant₁ m
  → invariant₁ (action m cs) :=
by
  simp [invariant₁]
  intros Hinv₁
  have H₁ : m.openedCourses \ cs ⊆ m.openedCourses := by
    apply Finset.sdiff_subset
  exact Finset.Subset.trans H₁ Hinv₁

theorem PO_safety₂ (cs : Finset Course) (m : M0 ctx):
  invariant₂ m
  → invariant₂ (action m cs) :=
by
  simp [invariant₂]
  intros Hinv₂
  have H₁ : (m.openedCourses \ cs).card ≤ m.openedCourses.card := by
    apply Finset_le_sdiff_sub
  apply le_trans (b:=Finset.card m.openedCourses) <;> assumption

/-!
In the original document, this event is used to introduce the notion
of convergent event, hence the convergence PO and proof follow.
-/

/-- The variant of (convergent) event `M0.CloseCourses`. -/
@[local simp]
def variant (m : M0 ctx) := m.openedCourses.card

/-- The non-increasing part of the convergence proof
for event `M0.CloseCourses`.

**Remark**: while the nonIncreasing (anticipated) part of the proof
is not mandatorily separated from the actual convergence proof, it
 is often a useful to do so.
-/
theorem PO_nonIncreasing (m : M0 ctx) (cs : Finset Course):
  variant (action m cs) ≤ variant m :=
by
  simp ; apply Finset_le_sdiff_sub

/-- PO: convergence proof for event `M0.CloseCourses`. -/
theorem PO_convergence (m : M0 ctx) (cs : Finset Course):
  guard m cs
  → variant (action m cs) < variant m :=
by
  simp
  intros Hgrd₁ Hgrd₂
  have Hgrd₁': cs.card ≤ m.openedCourses.card := by
    exact Finset.card_le_card Hgrd₁

  have H₁ := PO_nonIncreasing m cs ; simp at H₁
  apply lt_of_le_of_ne
  · assumption
  · intro Hcontra
    rw [Finset.card_sdiff] at Hcontra
    · have H₂: cs.card ≠ 0 := by
          intro Hzero
          have H₂ : cs = ∅ := by apply Finset.card_eq_zero.1 ; assumption
          contradiction
      have H₃ : cs.card = 0 := by
        apply Nat_sub_zero (a:=m.openedCourses.card)
        · have H₂' : 0 < cs.card := by exact Nat.pos_of_ne_zero H₂
          exact Nat.lt_of_lt_of_le H₂' Hgrd₁'
        · assumption
      contradiction
    · assumption

end CloseCourses

/-- Event: closing a specified set `cs` of opened courses. -/
def CloseCourses : ConvergentEvent Nat (M0 ctx) (Finset Course) Unit :=
newConvergentEvent' {
  guard := CloseCourses.guard
  action := fun m cs _ => CloseCourses.action m cs
  safety := fun m => by
    simp [Machine.invariant, -CloseCourses.guard, -CloseCourses.action]
    intros Hinv₁ Hinv₂ Hgrd _
    constructor
    · apply CloseCourses.PO_safety₁ ; assumption
    · apply CloseCourses.PO_safety₂ ; assumption
  variant := CloseCourses.variant
  convergence := fun cs m => by
    simp [Machine.invariant, -CloseCourses.guard]
    intros
    apply CloseCourses.PO_convergence
    assumption
  }

end M0

end CoursesSpec
