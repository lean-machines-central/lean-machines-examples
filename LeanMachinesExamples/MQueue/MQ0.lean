import LeanMachinesExamples.MQueue.Bounded
import LeanMachinesExamples.MQueue.Prioritized
import LeanMachinesExamples.MQueue.Clocked

import LeanMachines.Refinement.Functional.Basic
import LeanMachines.Refinement.Functional.Concrete

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
  messages : Finset (Message (instDec:=instDec))

instance [instDec: DecidableEq α]: Machine BoundedCtx (MQ0 α (instDec:=instDec) ctx) where
  context := ctx
  invariant mq := mq.messages.card ≤ ctx.maxCount
                  ∧ (∀ msg ∈ mq.messages, msg.timestamp < mq.clock)
                  ∧ (∀ msg₁ ∈ mq.messages, ∀ msg₂ ∈ mq.messages, msg₁.timestamp = msg₂.timestamp → msg₁ = msg₂)
  reset := { messages := ∅, clock := 0}

instance [instDec: DecidableEq α] : FRefinement (Bounded ctx) (MQ0 α ctx) where
  lift mq := { count := mq.messages.card }
  lift_safe mq := by simp [Machine.invariant] ; intros H _ _ ; exact H

/-  Cannot yet exploit this   (refined events could *not* be events but just instances of typeclasses)
instance [instDec: DecidableEq α] : FRefinement Clocked (MQ0 α ctx) where
  lift mq := { clock := mq.clock }
  lift_safe mq := by simp [Machine.invariant]
-/

def MQ0.Init [instDec: DecidableEq α] : InitREvent (Bounded ctx) (MQ0 α ctx) Unit Unit :=
  newInitREvent'' Bounded.Init {
    init := { messages := ∅, clock := 0}
    safety _ := by simp [Machine.invariant]
    strengthening _ := by simp [Machine.invariant, Bounded.Init]
    simulation _ := by simp [Machine.invariant, Refinement.refine, Bounded.Init, FRefinement.lift]
  }

def MQ0.Enqueue [instDec: DecidableEq α] : OrdinaryRDetEvent (Bounded ctx) (MQ0 α ctx) α Unit :=
  newConcreteFREvent' {
    guard mq x := mq.messages.card < ctx.maxCount ∧ ⟨x, mq.clock⟩ ∉ mq.messages
    action mq x := { messages := mq.messages ∪ {⟨x, mq.clock⟩},
                     clock := mq.clock + 1 }

    safety mq x := by
      simp [Machine.invariant]
      intros Hinv₁ Hinv₂ Hinv₃ Hgrd₁ Hgrd₂
      constructor
      · sorry
      constructor
      · intro msg Hmsg
        sorry
      · intros msg₁ Hmsg₁ msg₂ Hmsg₂ Hts
        sorry

    --feasibility mq x := by simp [Machine.invariant]
  }

end MQueue
