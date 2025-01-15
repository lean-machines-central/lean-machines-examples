import Mathlib.Tactic

import LeanMachines.Refinement.Functional.Basic
import LeanMachines.Refinement.Functional.Convergent
import LeanMachines.Refinement.Functional.NonDet.Convergent
import LeanMachines.Refinement.Relational.NonDet.Det.Convergent
import LeanMachines.Refinement.Functional.NonDet.Det.Convergent

import LeanMachinesExamples.Buffer.Buffer0

/-!

## Second refinement step

In this second step, the actual elements of the buffer at
managed within a `List`.  While elements are put in the
front of the list, they are retrieved in a non-deterministic way.

-/

namespace Buffer

/-- The state of the refined buffer machine. -/
structure B1 (ctx : BufContext) (α : Type) where
  /-- The contents of the buffer. -/
  data : List α

instance: Machine BufContext (B1 ctx α) where
  context := ctx
  invariant b1 := b1.data.length ≤ ctx.maxSize
  reset := { data := [] }

/-! We use the functional refinement principles of
LeanMachines, hence we need a way to *lift* the
concrete state.

Note that we cannot use the stronger form of
functional refinement, since elements are not
actually present at the abstract level.

-/

/-- Lifting the concrete state `b1` to the abstract type `B0`.
-/
@[simp]
def B1.lift (b1 : B1 ctx α) : B0 ctx :=
  { size := b1.data.length }

/-- Instantiation of the functional refinement requirements
(with trivial proofs).
-/
instance: FRefinement (B0 ctx) (B1 ctx α) where
  lift := B1.lift
  lift_safe := fun b1 => by simp [Machine.invariant]

/-- Event: Initialization of the buffer, refining `B0.Init`. -/
def B1.Init : InitREvent (B0 ctx) (B1 ctx α) Unit Unit :=
  newInitFREvent'' B0.Init {
    init _ := { data := [] }
    safety := fun _ => by simp [Machine.invariant]
    strengthening := by simp [B0.Init]
    simulation := by simp [FRefinement.lift, B0.Init]
  }

/-- Event: A refinement of `B0.Put` that prepends an element `x`
to the buffer `data`.
The event is proved convergent.
 -/
def B1.Put : ConvergentREvent Nat (B0 ctx) (B1 ctx α) α Unit Unit Unit :=
  newConvergentFREvent' B0.Put {
    guard := fun b1 _ => b1.data.length < ctx.maxSize
    action := fun b1 x _ => { data := x :: b1.data }

    lift_in := fun _ => ()

    safety := fun b1 x => by
      simp [Machine.invariant] ; intros ; linarith

    strengthening := fun b1 _ => by
      simp [Machine.invariant, B0.Put, FRefinement.lift]

    simulation := fun b1 _ => by
      simp [Machine.invariant, B0.Put, FRefinement.lift]

    variant := fun b1 => ctx.maxSize - b1.data.length

    convergence := fun b1 x => by
      simp [Machine.invariant] ; intros ; omega

  }

/-!
We illustrate here the fact that the same abstract event may be
refined multiple times at the concrete level.
-/

/-- Event: A refinement of `B0.Put` that appends an element `x`
to the buffer `data`.
The event is proved convergent.
 -/
def B1.PutLast : ConvergentREvent Nat (B0 ctx) (B1 ctx α) α Unit Unit Unit :=
  newConvergentFREvent' B0.Put {
    guard := fun b1 _ => b1.data.length < ctx.maxSize
    action := fun b1 x _ => { data := b1.data ++ [x] }

    lift_in := fun _ => ()

    safety := fun b1 x => by
      simp [Machine.invariant] ; intros ; linarith

    strengthening := fun b1 _ => by
      simp [Machine.invariant, B0.Put, FRefinement.lift]

    simulation := fun b1 _ => by
      simp [Machine.invariant, B0.Put, FRefinement.lift]

    variant := fun b1 => ctx.maxSize - b1.data.length

    convergence := fun b1 x => by
      simp [Machine.invariant] ; intros ; omega

  }


/-- Event: Removing an arbitrary element from the buffer.
This refines the abstract event `B0.Fetch`.
The event is convergent.
-/
def B1.Fetch : ConvergentRNDEvent Nat (B0 ctx) (B1 ctx α) Unit α Unit Unit :=
  newConvergentFRNDEvent B0.Fetch.toOrdinaryEvent.toOrdinaryNDEvent {
    guard := fun b1 _ => b1.data.length > 0
    effect := fun b1 _ _ (y, b1') =>
      y ∈ b1.data ∧ b1'.data.length = b1.data.length - 1
    safety := fun b1 _ => by simp [Machine.invariant] ; omega
    feasibility := fun b1 _ => by
      simp [Machine.invariant]
      cases b1.data <;> simp
    lift_in := id
    lift_out := fun _ => ()
    strengthening := fun b1 _ => by
      simp [Machine.invariant, B0.Fetch, FRefinement.lift, Refinement.refine]
    simulation := fun b1 _ => by
      simp [Machine.invariant, B0.Fetch, FRefinement.lift, Refinement.refine] ; omega
    variant := fun b1 => b1.data.length
    convergence := fun b1 _ => by
      simp [Machine.invariant]
      intros _ Hgrd _ b1' _ Heff₂
      omega
   }

/-- Event: deterministic refinement of `B0.Batch`.
The parameter is the list `xs` of elements to add.
-/
def B1.Batch : ConvergentRDetEvent Nat (B0 ctx) (B1 ctx α) (List α) Unit Unit Unit :=
  newConvergentRDetEvent' B0.Batch {
    guard := fun b1 xs => xs.length > 0 ∧ b1.data.length + xs.length ≤ ctx.maxSize
    action := fun b1 xs _ => { data := b1.data ++ xs }
    lift_in := fun _ => ()
    safety := fun b1 xs => by simp [Machine.invariant]
    strengthening := fun b1 xs => by
      simp [Machine.invariant, Refinement.refine, FRefinement.lift, B0.Batch]
      intros _ Hgrd Hlen
      cases xs
      case nil => contradiction
      case cons x xs =>
        simp at Hlen
        linarith
    simulation := fun b1 xs => by
      simp [Machine.invariant, Refinement.refine, FRefinement.lift, B0.Batch]
      intros _ Hgrd₁ Hgrd₂
      exists xs.length
    variant := fun b1 => ctx.maxSize - b1.data.length
    convergence := fun b1 xs => by
      simp [Machine.invariant]
      intros Hinv Hgrd₁ Hgrd₂
      cases xs
      case nil => contradiction
      case cons x xs =>
        simp at *
        omega
  }

/-- Event: Querying size of the buffer, refining `B0.GetSize`.
-/
def B1.GetSize : OrdinaryREvent (B0 ctx) (B1 ctx α) Unit Nat :=
  newREvent B0.GetSize {
    action := fun b1 _ _ => (b1.data.length, b1)
    lift_in := fun x => x
    lift_out := fun n => n
    safety := fun b1 _ => by simp
    strengthening := fun b1 _ => by
      simp [Machine.invariant, Refinement.refine, B0.GetSize]
    simulation := fun b1 _ => by
      simp [Machine.invariant, Refinement.refine, FRefinement.lift, B0.GetSize]
  }

end Buffer
