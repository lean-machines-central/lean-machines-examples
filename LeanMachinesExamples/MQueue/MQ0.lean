import LeanMachinesExamples.MQueue.Bounded
import LeanMachinesExamples.MQueue.Prioritized
import LeanMachinesExamples.MQueue.Clocked

import LeanMachines.Refinement.Functional.Basic
import LeanMachines.Refinement.Functional.Concrete

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SDiff


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

theorem Finset_notElem_card {α} [DecidableEq α] (xs : Finset α) (x : α):
  x ∉ xs → (xs ∪ {x}).card = xs.card + 1 :=
by
  intro Hx
  have Hdisj : Disjoint xs {x} := by
    exact Finset.disjoint_singleton_right.mpr Hx
  apply Finset.card_union_of_disjoint Hdisj


def MQ0.Enqueue [DecidableEq α] : OrdinaryREvent (Bounded ctx) (MQ0 α ctx) α Unit Unit Unit :=
  newFREvent' Bounded.Incr {
    lift_in := fun _ => ()
    guard mq x := mq.messages.card < ctx.maxCount ∧ ⟨x, mq.clock⟩ ∉ mq.messages
    action mq x := { messages := mq.messages ∪ {⟨x, mq.clock⟩},
                     clock := mq.clock + 1 }

    safety mq x := by
      simp [Machine.invariant]
      intros Hinv₁ Hinv₂ Hinv₃ Hgrd₁ Hgrd₂
      constructor
      · have Hcard : (mq.messages ∪ {⟨x, mq.clock⟩}).card = mq.messages.card + 1 := by
          apply Finset_notElem_card ; assumption
        rw [Hcard]
        exact Hgrd₁
      constructor
      · intro msg Hmsg
        cases Hmsg
        case _ Hmsg =>
          exact Nat.lt_succ_of_lt (Hinv₂ msg Hmsg)
        case _ Hmsg =>
          simp [Hmsg]
          exact Nat.lt_add_one mq.clock.val
      · intros msg₁ Hmsg₁ msg₂ Hmsg₂ Hts
        cases Hmsg₁
        case _ Hmsg₁ =>
          cases Hmsg₂
          case _ Hmsg₂ =>
            exact Hinv₃ msg₁ Hmsg₁ msg₂ Hmsg₂ Hts
          case _ Hmsg₂ =>
            have Hck₁ : msg₁.timestamp = mq.clock := by
              simp [Hmsg₂, Hts]
            have Hck₂ : msg₁.timestamp < mq.clock := by
              exact Hinv₂ msg₁ Hmsg₁
            rw [Hck₁] at Hck₂
            have Hck₂' : mq.clock.val < mq.clock.val := by
              exact Hck₂
            have Hcontra : False := by
              exact (lt_self_iff_false mq.clock.val).mp Hck₂'
            contradiction
        case _ Hmsg₁ =>
          cases Hmsg₂
          case _ Hmsg₂ =>
            have Hck₁ : msg₂.timestamp = mq.clock := by
              simp [Hmsg₁, ←Hts]
            have Hck₂ : msg₂.timestamp < mq.clock := by
              exact Hinv₂ msg₂ Hmsg₂
            rw [Hck₁] at Hck₂
            have Hck₂' : mq.clock.val < mq.clock.val := by
              exact Hck₂
            have Hcontra : False := by
              exact (lt_self_iff_false mq.clock.val).mp Hck₂'
            contradiction
          case _ Hmsg₂ =>
            simp [Hmsg₁, Hmsg₂]

    strengthening mq x := by
      simp [Machine.invariant, FRefinement.lift, Incr]
      intros _ _ _ Hgrd₁ _
      exact Hgrd₁

    simulation mq x := by
      simp [Machine.invariant, FRefinement.lift, Incr]
      intros Hinv₁ Hinv₂ Hinv₃ Hgrd₁ Hgrd₂
      have Hcard : (mq.messages ∪ {⟨x, mq.clock⟩}).card = mq.messages.card + 1 := by
          apply Finset_notElem_card ; exact Hgrd₂
      rw [Hcard]

  }

theorem Finset_card_sdiff_le [DecidableEq α] (t s : Finset α):
  (t \ s).card ≤ t.card :=
by
  have H₁ : (t \ s).card + s.card = (t ∪ s).card := by
    exact Finset.card_sdiff_add_card t s
  have H₂ : (t ∪ s).card ≤ t.card + s.card := by
    exact Finset.card_union_le t s
  have H₃ : (t \ s).card + s.card ≤ t.card + s.card := by
    exact le_of_eq_of_le H₁ H₂
  exact Nat.add_le_add_iff_right.mp H₃

def MQ0.Dequeue [DecidableEq α] : OrdinaryRNDEvent (Bounded ctx) (MQ0 α ctx) Unit α Unit Unit :=
  newRNDEvent Decr.toOrdinaryNDEvent {
    lift_in := id
    lift_out _ := ()
    guard mq _ := mq.messages ≠ ∅
    effect := fun mq _ (y, mq') =>
                ∃ msg ∈ mq.messages, y = msg.payload
                                     ∧ mq' = {mq with messages := mq.messages \ {msg}}

    safety mq _ := by
      simp [Machine.invariant]
      intros Hinv₁ Hinv₂ Hinv₃ Hgrd y mq' msg Hmsg Hy Hmq'
      have Hsub: mq'.messages ⊆ mq.messages := by
        simp [Hmq']
      constructor
      · simp [Hmq']
        have Hcard : (mq.messages \ {msg}).card ≤ mq.messages.card := by
          exact Finset_card_sdiff_le mq.messages {msg}
        exact Nat.le_trans Hcard Hinv₁
      constructor
      · intro msg' Hmsg'
        simp [Hmq']
        have Hmsg'' : msg' ∈ mq.messages := by
          exact Hsub Hmsg'
        exact Hinv₂ msg' (Hsub Hmsg')
      · intros msg₁ Hmsg₁ msg₂ Hmsg₂ Hts
        have Hmsg₁' : msg₁ ∈ mq.messages := by
          exact Hsub Hmsg₁
        have Hmsg₂' : msg₂ ∈ mq.messages := by
          exact Hsub Hmsg₂
        exact Hinv₃ msg₁ (Hsub Hmsg₁) msg₂ Hmsg₂' Hts

    feasibility mq _ := by
      simp [Machine.invariant]
      intros Hinv₁ Hinv₂ Hinv₃ Hgrd
      have Hex : ∃ msg, msg ∈ mq.messages := by
        refine Finset.Nonempty.exists_mem ?_
        exact Finset.nonempty_iff_ne_empty.mpr Hgrd
      obtain ⟨msg, Hmsg⟩ := Hex
      exists msg.payload
      exists {clock := mq.clock, messages := mq.messages \ {msg}}
      exists msg

    strengthening mq _ := by
      simp [Machine.invariant, Refinement.refine, Decr, FRefinement.lift]
      intros Hinv₁ Hinv₂ Hinv₃ Hgrd
      exact Finset.nonempty_iff_ne_empty.mpr Hgrd

    simulation mq _ := by
      simp [Machine.invariant, Refinement.refine, Decr, FRefinement.lift]
      intros Hinv₁ Hinv₂ Hinv₃ Hgrd y mq' msg Hmsg Hy Hmq'
      simp [Hmq']
      have Hcard : (mq.messages \ {msg}).card = mq.messages.card - 1 := by
        apply Finset.card_sdiff
        exact Finset.singleton_subset_iff.mpr Hmsg
      simp [Hcard]

  }

end MQueue
