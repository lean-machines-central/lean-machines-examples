
import LeanMachines.Refinement.Strong.Basic
import LeanMachines.Refinement.Strong.Convergent

import LeanMachinesExamples.Buffer.Buffer0

/-!

# Experiment: Simultaneous refinement

Unlike Event-B,  the LeanMachines framework allows a concrete machine
to refine multiple abstract machines in a simultaneous way.

To illustrate this, as a preliminary experiment, we define a variant
of the abstract machine `Buffer0` that requires a button to be pushed
upon inserting elements (i.e. increasing the number of elements at
this level of abstraction). Put in other term, we construct a
 counter controlled by a push button.

-/

namespace Buffer

/-!

## Step 1 : the push button

First, we give a simplistic definition of a push button machine.

-/

structure Button where
  pushed : Bool

instance: Machine Unit Button where
  context := ()
  invariant _ := True
  default := { pushed := false }

def Button.Push : OrdinaryEvent Button Unit Unit :=
  newEvent'' {
    guard := fun st => ¬ st.pushed
    action := fun _ _ => { pushed := true }
    safety := fun st => by simp [Machine.invariant]
  }

def Button.Release : OrdinaryEvent Button Unit Unit :=
  newEvent'' {
    guard := fun st => st.pushed
    action := fun _ _ => { pushed := false }
    safety := fun st => by simp [Machine.invariant]
  }

/-!

## Step 2 : the Push Buffer

The Push Buffer state is simply the merging of two
abstract states: the abstract buffer `B0` and the `Button`.

-/

structure PushBuffer (ctx : BufContext)
  extends B0 ctx, Button where

/-!
Of course the machine itself merges the invariants and default states.
-/

instance: Machine BufContext (PushBuffer ctx) where
  context := ctx
  invariant := fun pb => Machine.invariant pb.toB0 ∧ Machine.invariant pb.toButton
  default := { toB0 := default, toButton := default }

/-!
Now we are at the interesting place, with the definition of two
(strong) refinement instances: one refinement of the abstract buffer,
 and another distinct one for the push button.
-/

instance: SRefinement (B0 ctx) (PushBuffer ctx) where
  lift := fun pb => pb.toB0
  unlift := fun pb b0' => { pb with toB0 := b0' }
  lift_safe := fun pb => by simp [Machine.invariant]
  lift_unlift := fun pb b0' => by simp [Machine.invariant]
  lu_default := fun b0' => by simp [Machine.invariant]

instance: SRefinement Button (PushBuffer ctx) where
  lift := fun pb => pb.toButton
  unlift := fun pb pb0' => { pb with toButton := pb0' }
  lift_safe := fun pb => by simp [Machine.invariant]
  lift_unlift := fun pb b0' => by simp [Machine.invariant]
  lu_default := fun b0' => by simp [Machine.invariant]

/-!
Of course, events from both "parents" can be refined as well.
For example, we can refine `B0.Put` by requiring at the same time
a guard condition for the buffer part, and another one for the
putton. As an example, the following says that an element can only
be added to the buffer if the button is pushed.
-/

def PB.PutBuf : OrdinaryREvent (B0 ctx) (PushBuffer ctx) Unit Unit :=
  newSREvent'' B0.Put {
    guard := fun (pb : PushBuffer ctx) => pb.size < ctx.maxSize ∧ pb.pushed
    action := fun pb _ => { pb with size := pb.size + 1 }
    safety := fun pb => by
      simp [Machine.invariant] ; intros ; assumption
    strengthening := fun pb => by
      simp [Machine.invariant] ; intros ; assumption
    simulation := fun bp => by
      simp [Machine.invariant] ; intros ; rfl
  }

/-!
  Note that there is a lot of redundancy here. It would be better to rely on
  more generic definitions but we will not care for this simplistic illustration.
-/

/-!
Finally, we can also refine the push action by requiring the buffer to have
enough room for at least one element. Said differently, the button can only
be pushed is the buffer is not full.
-/

def PB.Push : OrdinaryREvent Button (PushBuffer ctx) Unit Unit :=
  newREvent'' Button.Push {
    guard := fun st => ¬ st.pushed ∧ st.size < ctx.maxSize
    action := fun st _ => { st with pushed := true }
    safety := fun st => by
      simp [Machine.invariant] ; intros ; assumption
    strengthening := fun st => by
      simp [Machine.invariant, Button.Push, Refinement.refine] ; intros ; assumption
    simulation := fun st => by
      simp [Machine.invariant, Button.Push, Refinement.refine] ; intros ; rfl
  }


end Buffer
