import LeanMachinesExamples.MQueue.Bounded
import LeanMachinesExamples.MQueue.Prioritized
import LeanMachinesExamples.MQueue.Clocked

import LeanMachines.Refinement.Functional.Basic
import LeanMachines.Refinement.Functional.NonDet.Concrete

namespace MQueue

open Bounded
open Prioritized
open Clocked

structure Message (α : Type 0) [instDec: DecidableEq α] where
  payload : α
  timestamp : Clock

instance [instDec: DecidableEq α] (m₁ m₂ : @Message α instDec): Decidable (m₁ = m₂) :=
  by cases m₁
     case mk x₁ t₁ =>
     cases m₂
     case mk x₂ t₂ =>
       simp
       exact instDecidableAnd

structure MQ0 (α : Type 0) [instDec: DecidableEq α] (ctx : BoundedCtx)
    extends Clocked where
  queue : List (Message (instDec:=instDec))

instance [instDec: DecidableEq α]: Machine BoundedCtx (MQ0 α (instDec:=instDec) ctx) where
  context := ctx
  invariant mq := mq.queue.length ≤ ctx.maxCount ∧ ∀ msg ∈ mq.queue, msg.timestamp < mq.clock
  reset := { queue := [], clock := 0}

instance [instDec: DecidableEq α] : FRefinement (Bounded ctx) (MQ0 α ctx) where
  lift mq := { count := mq.queue.length }
  lift_safe mq := by simp [Machine.invariant] ; intros H _ ; exact H

/-  Cannot yet exploit this   (refined events could *not* be events but just instances of typeclasses)
instance [instDec: DecidableEq α] : FRefinement Clocked (MQ0 α ctx) where
  lift mq := { clock := mq.clock }
  lift_safe mq := by simp [Machine.invariant]
-/

def MQ0.Init [instDec: DecidableEq α] : InitREvent (Bounded ctx) (MQ0 α ctx) Unit Unit :=
  newInitREvent'' Bounded.Init {
    init := { queue := [], clock := 0}
    safety _ := by simp [Machine.invariant]
    strengthening _ := by simp [Machine.invariant, Bounded.Init]
    simulation _ := by simp [Machine.invariant, Refinement.refine, Bounded.Init, FRefinement.lift]
  }

def MQ0.Enqueue [instDec: DecidableEq α] : OrdinaryRNDEvent (Bounded ctx) (MQ0 α ctx) α Unit :=
  newConcreteFRNDEvent' {
    guard mq x := mq.queue.length < ctx.maxCount ∧ ⟨x, mq.clock⟩ ∉ mq.queue
    effect mq x mq' := (∀ msg ∈ mq.queue, msg ∈ mq'.queue)
                          ∧ ⟨x, mq.clock⟩ ∈ mq'.queue
                          ∧ mq'.clock = mq.clock + 1

    safety mq data := by
  }

end MQueue
