import LeanMachinesExamples.MQueue.Bounded
import LeanMachinesExamples.MQueue.Prioritized
import LeanMachinesExamples.MQueue.Clocked
import LeanMachinesExamples.MQueue.MQ0

import LeanMachines.Refinement.Functional.Basic
import LeanMachines.Refinement.Functional.Concrete

import LeanMachines.Refinement.Strong.Basic

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

--instance [DecidableEq α]: LT (Message α) where
--  lt m₁ m₂ := (m₁.prio < m₂.prio) ∨ (m₁.prio = m₂.prio ∧ m₁.timestamp < m₂.timestamp)

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
  default := { messages := ∅, clock := 0}

theorem MQ1.clock_free [DecidableEq α] (mq : MQ1 α ctx):
  Machine.invariant mq → ∀ x, ∀ p, ⟨⟨x, mq.clock⟩, p⟩ ∉ mq.messages :=
by
  simp [Machine.invariant]
  intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ x p Hin
  have Hinv₂' := Hinv₂ ⟨⟨x, mq.clock⟩, p⟩ Hin
  simp at Hinv₂' -- contradiction

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

def injectPrio [DecidableEq α] (msg0 : Message0 α) : Message α :=
  { msg0 with prio := default }

def unliftMessage [DecidableEq α]: Message0 α ↪ Message α :=
  { toFun := injectPrio
    inj' := by simp [Function.Injective, injectPrio]
  }

def unliftMessages [DecidableEq α] (msg0s : Finset (Message0 α)) : Finset (Message α) :=
  msg0s.map unliftMessage

def newMessages [DecidableEq α] (mq0 : MQ0 α ctx) (mq0' : MQ0 α ctx) :=
  mq0'.messages \ mq0.messages

def MQ1.unlift [DecidableEq α] (mq1 : MQ1 α ctx) (mq0' : MQ0 α ctx.toBoundedCtx) : MQ1 α ctx :=
 { clock := mq0'.clock
   messages := mq1.messages ∪ (unliftMessages (newMessages mq1.lift mq0')) }

instance [instDec: DecidableEq α] : SRefinement (MQ0 α ctx.toBoundedCtx) (MQ1 α ctx) where
  unlift := MQ1.unlift
  lift_unlift := by
    intros mq1 mq0' Hinv Hainv
    simp [FRefinement.lift, MQ1.unlift, newMessages]
    sorry -- TODO
  lu_default := by
    simp [FRefinement.lift, MQ1.unlift, default]
    sorry -- TODO

def MQ1.Init [instDec: DecidableEq α] : InitREvent (MQ0 α ctx.toBoundedCtx) (MQ1 α ctx) Unit Unit :=
  newInitREvent'' MQ0.Init.toInitEvent {
    init _ := { messages := ∅, clock := 0}
    safety _ := by simp [Machine.invariant]
    strengthening _ := by simp [Machine.invariant, MQ0.Init]
    simulation _ := by simp [Machine.invariant, Refinement.refine, MQ0.Init, FRefinement.lift]
  }

def MQ1.Enqueue [DecidableEq α] : OrdinaryREvent (MQ0 α ctx.toBoundedCtx) (MQ1 α ctx) (α × Prio) Unit α Unit :=
  newFREvent' MQ0.Enqueue.toOrdinaryEvent {
    lift_in := fun (x, _) => x
    guard := fun mq (x, px) => mq.messages.card < ctx.maxCount
                               ∧ ctx.minPrio ≤ px ∧ px ≤ ctx.maxPrio
    action := fun mq (x, px) _  =>
                { messages := mq.messages ∪ {⟨⟨x, mq.clock⟩, px⟩},
                  clock := mq.clock + 1 }

    safety := fun mq (x, px) => by
      intro Hinv
      have Hclk := MQ1.clock_free mq Hinv
      revert Hinv
      simp [Machine.invariant]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hgrd₁ Hgrd₂ Hgrd₃
      constructor
      · have Hcard : (mq.messages ∪ {⟨⟨x, mq.clock⟩, px⟩}).card = mq.messages.card + 1 := by
          apply Finset_notElem_card
          intro Hcontra
          exact Hclk x px Hcontra
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
          exact ⟨Hgrd₂, Hgrd₃⟩

    strengthening := fun mq (x, px) => by
      simp [Machine.invariant, FRefinement.lift, MQ0.Enqueue]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hgrd₁ Hgrd₂ Hgrd₃
      exact Hgrd₁

    simulation := fun mq (x, px) => by
      simp [Machine.invariant, FRefinement.lift, MQ0.Enqueue]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hgrd₁ Hgrd₂ Hgrd₃
      simp [Finset.map_union]

  }

def MQ1.priorities [DecidableEq α] (mq : MQ1 α ctx) : Finset Prio :=
  Finset.fold (·∪·) ∅ (fun msg => {msg.prio}) mq.messages

theorem MQ1_prios_in [DecidableEq α] (mq : MQ1 α ctx):
  ∀ msg ∈ mq.messages, msg.prio ∈ mq.priorities :=
by
  simp [MQ1.priorities]
  induction mq.messages using Finset.induction_on
  case empty => simp
  case insert msg messages Hmsg Hind =>
    simp
    intros msg' Hmsg'
    right
    exact Hind msg' Hmsg'

def MQ1.maxPrio [DecidableEq α] (mq : MQ1 α ctx) : Prio :=
  Finset.fold max 0 id mq.priorities

theorem MQ1.maxPrio_max [DecidableEq α] (mq : MQ1 α ctx) :
  ∀ msg ∈ mq.messages, msg.prio ≤ mq.maxPrio :=
by
  simp [MQ1.maxPrio]
  intro msg Hmsg
  rw [@Finset.le_fold_max]
  right
  exists msg.prio
  constructor
  · exact MQ1_prios_in mq msg Hmsg
  · exact Preorder.le_refl msg.prio

theorem MQ1.maxPrio_in [DecidableEq α] (mq : MQ1 α ctx):
  Finset.Nonempty mq.priorities
  → mq.maxPrio ∈ mq.priorities :=
by
  simp [maxPrio]
  induction mq.priorities using Finset.induction
  case empty => simp
  case insert p ps Hp Hind =>
    rw [@Finset.mem_insert]
    intro Hne
    by_cases ps.Nonempty
    case pos Hne' =>
      have Hind' := Hind Hne'
      by_cases p ≤ Finset.fold max 0 (fun x => x) ps
      case pos Hp =>
        simp [Hp]
        right
        exact Hind Hne'
      case neg Hp =>
        simp [Hp]
        left
        exact le_of_not_ge Hp

    case neg He =>
      simp [*] at *
      simp [He]
      apply Prio_lift_le
      exact StrictMono.minimal_preimage_bot (fun ⦃a b⦄ a => a) rfl p.prio

theorem MQ1.msgEx [DecidableEq α] (mq : MQ1 α ctx):
  ∀ prio ∈ mq.priorities, ∃ msg ∈ mq.messages, msg.prio = prio :=
by
  unfold MQ1.priorities
  induction mq.messages using Finset.induction
  case empty => simp
  case insert msg messages Hmsg Hind =>
    simp
    intro msg' Hmsg'
    exact Or.symm (Or.intro_left (msg.prio = msg') (Hind msg' Hmsg'))

def MQ1.Nonempty  [DecidableEq α] (mq : MQ1 α ctx):
  Finset.Nonempty mq.messages
  → Finset.Nonempty mq.priorities :=
by
  intro Hne
  by_cases mq.priorities = ∅
  case pos Hpos =>
    have Hex : ∃ msg, msg ∈ mq.messages := by
      exact Hne
    obtain ⟨msg, Hmsg⟩ := Hex
    have Hprio : msg.prio ∈ mq.priorities := by
      exact MQ1_prios_in mq msg Hmsg
    simp [Hpos] at Hprio
  case neg Hneg =>
    exact Finset.nonempty_iff_ne_empty.mpr Hneg

def MQ1.maxElemEx [DecidableEq α] (mq : MQ1 α ctx):
  Finset.Nonempty mq.messages
  → ∃ msg ∈ mq.messages, msg.prio = mq.maxPrio :=
by
  intro Hne
  refine msgEx mq mq.maxPrio ?_
  refine maxPrio_in mq ?_
  exact Nonempty mq Hne

def Finset_map_sdiff [DecidableEq α] [DecidableEq β] (s t : Finset α) (f : α ↪ β):
  Finset.map f (s \ t) = (Finset.map f s) \ (Finset.map f t) :=
by
  induction s using Finset.induction
  case empty => simp
  case insert x xs Hx Hind =>
    simp [Hx]
    by_cases f x ∈ Finset.map f xs
    case pos Hfx =>
      have Hx' : x ∈ xs := by exact (Finset.mem_map' f).mp Hfx
      contradiction
    case neg Hfx =>
      by_cases x ∈ t
      case pos Hxx =>
        rw [Finset.insert_sdiff_of_mem xs Hxx]
        simp [Hind]
        have Hfx' : f x ∈ Finset.map f t := by
          exact (Finset.mem_map' f).mpr Hxx
        exact Eq.symm (Finset.insert_sdiff_of_mem (Finset.map f xs) Hfx')
      case neg Hxx =>
        rw [Finset.insert_sdiff_of_not_mem xs Hxx]
        rw [@Finset.map_insert]
        simp [Hind]
        have Hfx' : f x ∉ Finset.map f t := by
          rw [@Finset.mem_map']
          assumption
        exact Eq.symm (Finset.insert_sdiff_of_not_mem (Finset.map f xs) Hfx')

def MQ1.Dequeue [DecidableEq α] : OrdinaryRNDEvent (MQ0 α ctx.toBoundedCtx) (MQ1 α ctx) Unit (α × Prio) Unit α :=
  newRNDEvent MQ0.Dequeue.toOrdinaryNDEvent {
    lift_in := id
    lift_out := fun (x, _) => x
    guard mq _ := mq.messages ≠ ∅
    effect := fun mq _ _ ((y, py), mq') =>
                ∃ msg ∈ mq.messages, y = msg.payload ∧ py = msg.prio
                                     ∧ mq' = {mq with messages := mq.messages \ {msg}}
                                     ∧ ∀ msg' ∈ mq.messages, msg' ≠ msg → msg'.prio ≤ msg.prio

    safety mq _ := by
      simp [Machine.invariant]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hgrd y py mq' msg Hmsg Hy Hpy Hmq' Hprio
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
      constructor
      · intros msg₁ Hmsg₁ msg₂ Hmsg₂ Hts
        have Hmsg₁' : msg₁ ∈ mq.messages := by
          exact Hsub Hmsg₁
        have Hmsg₂' : msg₂ ∈ mq.messages := by
          exact Hsub Hmsg₂
        exact Hinv₃ msg₁ (Hsub Hmsg₁) msg₂ Hmsg₂' Hts
      · intros msg Hmsg
        exact Hinv₄ msg (Hsub Hmsg)

    feasibility mq x := by
      simp [Machine.invariant]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hgrd
      have Hne : mq.messages.Nonempty := by exact Finset.nonempty_iff_ne_empty.mpr Hgrd
      obtain ⟨msg, ⟨Hmsg, Hprio⟩⟩ := MQ1.maxElemEx mq Hne
      exists msg.payload ; exists msg.prio
      exists { toClocked := mq.toClocked, messages := mq.messages \ {msg} }
      exists msg
      simp [*]
      intros msg' Hmsg' Hinj
      exact maxPrio_max mq msg' Hmsg'

    strengthening mq _ := by
      simp [Machine.invariant, Refinement.refine, MQ0.Dequeue, FRefinement.lift]

    simulation mq _ := by
      simp [Machine.invariant, Refinement.refine, MQ0.Dequeue, FRefinement.lift]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hgrd y py mq' msg Hmsg Hy Hpy Hmq' Hprio
      simp [Hmq']
      exists msg
      simp [Hmsg, Hy]
      simp [Finset_map_sdiff]

  }

end MQueue
