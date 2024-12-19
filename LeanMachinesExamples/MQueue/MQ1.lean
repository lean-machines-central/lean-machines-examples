import LeanMachinesExamples.MQueue.Bounded
import LeanMachinesExamples.MQueue.Prioritized
import LeanMachinesExamples.MQueue.Clocked
import LeanMachinesExamples.MQueue.MQ0

import LeanMachines.Refinement.Functional.Basic
import LeanMachines.Refinement.Functional.Concrete

namespace MQueue

open Bounded
open Prioritized
open Clocked

structure MQContext extends BoundedCtx, PrioCtx

structure Message (α : Type 0) [instDec: DecidableEq α] extends Message0 α where
  prio : Prio

instance [instDec: DecidableEq α] (m₁ m₂ : @Message α instDec): Decidable (m₁ = m₂) :=
  by cases m₁ ; cases m₂
     simp
     exact instDecidableAnd

instance [DecidableEq α]: LT (Message α) where
  lt m₁ m₂ := (m₁.prio < m₂.prio) ∨ (m₁.prio = m₂.prio ∧ m₁.timestamp < m₂.timestamp)

structure MQ1 (α : Type 0) [instDec: DecidableEq α] (ctx : MQContext)
    extends Clocked where
  messages : Finset (Message α)

-- We axiomatize the fact that lifting messages is injective
axiom liftMessage_inj_ax {α} [instDec: DecidableEq α]:
  Function.Injective (Message.toMessage0 (instDec:=instDec))

@[simp]
def liftMessage [DecidableEq α] : Function.Embedding (Message α) (Message0 α) :=
  {
    toFun := Message.toMessage0
    inj' := liftMessage_inj_ax
  }

@[simp]
def MQ1.lift [DecidableEq α] (mq : MQ1 α ctx) : MQ0 α ctx.toBoundedCtx :=
  {clock := mq.clock, messages := Finset.map liftMessage mq.messages}

instance [instDec: DecidableEq α]: Machine MQContext (MQ1 α (instDec:=instDec) ctx) where
  context := ctx
  invariant mq := mq.messages.card ≤ ctx.maxCount
                  ∧ (∀ msg ∈ mq.messages, msg.timestamp < mq.clock)
                  ∧ (∀ msg₁ ∈ mq.messages, ∀ msg₂ ∈ mq.messages, msg₁.timestamp = msg₂.timestamp → msg₁ = msg₂)
                  ∧ (∀ msg ∈ mq.messages, ctx.minPrio ≤ msg.prio ∧ msg.prio ≤ ctx.maxPrio)
  reset := { messages := ∅, clock := 0}

instance [instDec: DecidableEq α] : FRefinement (MQ0 α ctx.toBoundedCtx) (MQ1 α ctx) where
  lift := MQ1.lift
  lift_safe mq := by
    simp [Machine.invariant]
    intros Hinv₁ Hinv₂ Hinv₃ Hinv₄
    constructor
    · exact Hinv₁
    constructor
    · intros msg Hmsg ; exact Hinv₂ msg Hmsg
    · intros msg₁ Hmsg₁ msg₂ Hmsg₂ Hts
      exact congrArg Message.toMessage0 (Hinv₃ msg₁ Hmsg₁ msg₂ Hmsg₂ Hts)

def MQ1.Init [instDec: DecidableEq α] : InitREvent (MQ0 α ctx.toBoundedCtx) (MQ1 α ctx) Unit Unit :=
  newInitREvent'' MQ0.Init.toInitEvent {
    init := { messages := ∅, clock := 0}
    safety _ := by simp [Machine.invariant]
    strengthening _ := by simp [Machine.invariant, MQ0.Init]
    simulation _ := by simp [Machine.invariant, Refinement.refine, MQ0.Init, FRefinement.lift]
  }

def MQ1.Enqueue [DecidableEq α] : OrdinaryREvent (MQ0 α ctx.toBoundedCtx) (MQ1 α ctx) (α × Prio) Unit α Unit :=
  newFREvent' MQ0.Enqueue.toOrdinaryEvent {
    lift_in := fun (x, _) => x
    guard := fun mq (x, px) => mq.messages.card < ctx.maxCount
                               ∧ (∀ msg ∈ mq.messages, msg.timestamp ≠ mq.clock)
                               ∧ ctx.minPrio ≤ px ∧ px ≤ ctx.maxPrio
    action := fun mq (x, px) =>
                { messages := mq.messages ∪ {⟨⟨x, mq.clock⟩, px⟩},
                  clock := mq.clock + 1 }

    safety := fun mq (x, px) => by
      simp [Machine.invariant]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hgrd₁ Hgrd₂ Hgrd₃ Hgrd₄
      constructor
      · have Hcard : (mq.messages ∪ {⟨⟨x, mq.clock⟩, px⟩}).card = mq.messages.card + 1 := by
          apply Finset_notElem_card
          intro Hcontra
          exact Hgrd₂ { payload := x, timestamp := mq.clock, prio := px } Hcontra rfl
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
      constructor
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
      · intros msg Hmsg
        cases Hmsg
        case _ Hmsg =>
          exact Hinv₄ msg Hmsg
        case _ Hmsg =>
          simp [Hmsg]
          exact ⟨Hgrd₃, Hgrd₄⟩

    strengthening := fun mq (x, px) => by
      simp [Machine.invariant, FRefinement.lift, MQ0.Enqueue]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hgrd₁ Hgrd₂ Hgrd₃ Hgrd₄
      constructor
      · exact Hgrd₁
      · intros msg Hmsg Hcontra
        have Hclk : msg.timestamp < mq.clock := by
          exact Hinv₂ msg Hmsg
        simp [Hcontra] at Hclk
        have Hclk' : mq.clock.val < mq.clock.val := by
              exact Hclk
        exact (lt_self_iff_false mq.clock.val).mp Hclk'

    simulation := fun mq (x, px) => by
      simp [Machine.invariant, FRefinement.lift, MQ0.Enqueue]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hgrd₁ Hgrd₂ Hgrd₃ Hgrd₄
      simp [Finset.map_union]

  }

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
