
import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary

/-!

# The Event-B Bridge example

This example specification is a version of the infamous
Event-B Bridge model of the Event-B book (chapter ).
Only the abstract machine and the two first refinement steps
have been formalized for now.

While more feature of the LeanMachines framework could have
been used in practice (e.g. functional refinement), we sticked
to "standard" Event-B features. There are of course notable
differences, among them:

 - the use of type theory rather than untyped set theory
 (although we rely on Mathlib's typed finite sets)

 - proof details are of course different (although the proof "strategy"
  is the same as in the book)

 - the state variables and the event names have been made more explicit

Note that it is best to follow the Bridge specification with a copy of the
 Event-B book aside.

-/

/-!

## The abstract machine

-/

namespace BridgeSpec

/-- The context of the Bridge specification.
 -/
structure Context where
  /-- Parameter : Maximum number of cars present on the Bridge. -/
  maxCars : Nat
  maxCars_pos : maxCars > 0

/-- The state of the abstract Bridge machine. -/
structure Bridge0 (ctx : Context) where
  /-- Number of cars currently present on the Bridge -/
  nbCars : Nat

/-- The single invariant of the abstract bridge:
The current number of cars is less than the allowed maximum.
 -/
@[simp]
def Bridge0.invariant (b0 : Bridge0 ctx) : Prop :=
  b0.nbCars ≤ ctx.maxCars

/-- The machine description of the abstract Bridge. -/
instance: Machine Context (Bridge0 ctx) where
  context := ctx
  invariant m := Bridge0.invariant m
  default := { nbCars := 0 }

namespace Bridge0

/-- Initialization event: empty bridge -/
def Init : InitEvent (Bridge0 ctx) Unit Unit := newInitEvent'' {
  init _ := { nbCars := 0 }
  safety := by simp [Machine.invariant]
}

/-- Event: a new car enters the Bridge from mainland. -/
def EnterFromMainland : OrdinaryEvent (Bridge0 ctx) Unit Unit := newEvent'' {
  guard := fun m => m.nbCars < ctx.maxCars
  action := fun m _ => { nbCars := m.nbCars + 1}
  safety := fun m => by
    simp [Machine.invariant]
    intros _ Hgrd
    exact Hgrd

}

/-- Event: a car exits the Bridge towards the mainland. -/
def LeaveToMainland : OrdinaryEvent (Bridge0 ctx) Unit Unit := newEvent'' {
  guard := fun m => m.nbCars > 0
  action := fun m _ => { nbCars := m.nbCars - 1}
  safety := fun m => by
    simp [Machine.invariant]
    intros Hinv _  -- remark : 0 - 1 = 0
    omega
}

/-- Deadlock fredom property expressed as a theorem.
 -/
theorem deadlockFreedom (m : Bridge0 ctx):
  Machine.invariant m
  → EnterFromMainland.guard m () ∨ LeaveToMainland.guard m () :=
by
  simp [Machine.invariant, EnterFromMainland, LeaveToMainland, newEvent']
  intro Hinv
  have Hctx := ctx.maxCars_pos
  omega

end Bridge0

end BridgeSpec
