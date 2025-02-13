import Mathlib.Data.Finset.Max

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

def liftMessages [DecidableEq α] (ms : Finset (Message α)) : Finset (Message0 α) :=
  Finset.map liftMessage ms

theorem liftMessages_in [DecidableEq α] (ms : Finset (Message α)):
  ∀ msg ∈ ms, (liftMessage msg) ∈ liftMessages ms :=
by
  simp [liftMessage, liftMessages]
  intros msg Hmsg
  exists msg

@[simp]
def MQ1.lift [DecidableEq α] (mq : MQ1 α ctx) : MQ0 α ctx.toBoundedCtx :=
  {clock := mq.clock, messages := Finset.map liftMessage mq.messages}

theorem MQ1.lift_in [DecidableEq α] (mq : MQ1 α ctx):
  ∀ msg ∈ mq.messages, (liftMessage msg) ∈ mq.lift.messages :=
by
  apply liftMessages_in

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

theorem unliftMessages_sdiff [DecidableEq α] (ms1 ms2 : Finset (Message0 α)):
  Disjoint ms1 ms2
  → unliftMessages (ms1 \ ms2) = (unliftMessages ms1) \ (unliftMessages ms2) :=
by
  intro Hdisj
  rw [@Finset.Subset.antisymm_iff]
  constructor
  case left =>
    simp [unliftMessages]
    rw [@Finset.subset_sdiff]
    constructor
    case left =>
      refine GCongr.finsetMap_subset ?_
      exact Finset.sdiff_subset
    case right =>
      refine (Finset.disjoint_map unliftMessage).mpr ?_
      exact Finset.sdiff_disjoint
  case right =>
    simp [unliftMessages]
    refine Finset.subset_iff.mpr ?_
    intros msg Hmsg
    rw [Finset.sdiff_eq_self_of_disjoint Hdisj]
    by_cases ms1 = ∅
    case pos Hpos =>
      rw [Hpos] at Hmsg
      simp at Hmsg
    case neg Hneg =>
      simp at Hmsg
      obtain ⟨Hmsg₁, Hmsg₂⟩ := Hmsg
      obtain ⟨msg', Hmsg'₁, Hmsg'₂⟩ := Hmsg₁
      simp [unliftMessage] at Hmsg'₂
      simp [unliftMessage]
      exists msg'

theorem unliftMessages_in [DecidableEq α] (msg0s : Finset (Message0 α)):
  ∀ msg0 ∈ msg0s, unliftMessage msg0 ∈ unliftMessages msg0s :=
by
  intros msg0 Hmsg0
  simp [unliftMessage, unliftMessages]
  exists msg0

theorem liftMessage_roundTrip [DecidableEq α] (ms : Finset (Message0 α)):
  liftMessages (unliftMessages ms) = ms :=
by
  simp [liftMessages, unliftMessages]
  refine Finset.ext_iff.mpr ?_
  intro msg
  constructor
  case mp =>
    simp [unliftMessage, injectPrio]
  case mpr =>
    intro Hmsg
    simp [unliftMessage, injectPrio]
    assumption

def newMessages [DecidableEq α] (mq0 mq0' : MQ0 α ctx) :=
  mq0'.messages \ mq0.messages

def delMessages [DecidableEq α] (mq0 mq0' : MQ0 α ctx) :=
  mq0.messages \ mq0'.messages

theorem newDelMessages_Disjoint [DecidableEq α] (mq0 mq0' : MQ0 α ctx):
  Disjoint (newMessages mq0 mq0')
           (delMessages mq0 mq0') :=
by
  simp  [newMessages, delMessages]
  exact disjoint_sdiff_sdiff

theorem newDelMessages_Disjoint' [DecidableEq α] (mq0 mq0' : MQ0 α ctx):
  Disjoint (unliftMessages (newMessages mq0 mq0'))
           (unliftMessages (delMessages mq0 mq0')) :=
by
  rw [@Finset.disjoint_iff_ne]
  intros msg₁ Hmsg₁ msg₂ Hmsg₂
  have Hmsg₁': liftMessage msg₁ ∈ liftMessages (unliftMessages (newMessages mq0 mq0')) := by
    exact liftMessages_in (unliftMessages (newMessages mq0 mq0')) msg₁ Hmsg₁
  have Hmsg₂': liftMessage msg₂ ∈ liftMessages (unliftMessages (delMessages mq0 mq0')) := by
    exact liftMessages_in (unliftMessages (delMessages mq0 mq0')) msg₂ Hmsg₂
  simp at Hmsg₁'
  simp [liftMessage_roundTrip] at Hmsg₁' Hmsg₂'
  simp [newMessages] at Hmsg₁'
  simp [delMessages] at Hmsg₂'




def updateMessages [DecidableEq α] (mq1 : MQ1 α ctx) (mq0' : MQ0 α ctx.toBoundedCtx) :=
  (mq1.messages \ (unliftMessages (delMessages mq1.lift mq0')))
  ∪ (unliftMessages (newMessages mq1.lift mq0'))

theorem updateMessages_prop₁ [DecidableEq α] (mq1 : MQ1 α ctx) (mq0' : MQ0 α ctx.toBoundedCtx):
  ∀ msg0 ∈ mq0'.messages,
    msg0 ∉ mq1.lift.messages
    → (unliftMessage msg0) ∈ updateMessages mq1 mq0' :=
by
  sorry

def MQ1.unlift [DecidableEq α] (mq1 : MQ1 α ctx) (mq0' : MQ0 α ctx.toBoundedCtx) : MQ1 α ctx :=
 { clock := mq0'.clock
   messages := (mq1.messages \ (unliftMessages (delMessages mq1.lift mq0'))) ∪ (unliftMessages (newMessages mq1.lift mq0')) }

theorem MQ1.unlift_prop₁ [DecidableEq α] (mq1 : MQ1 α ctx) (mq0' : MQ0 α ctx.toBoundedCtx):
  unliftMessages mq0'.messages ⊆ (mq1.unlift mq0').messages :=
by
  sorry


instance [instDec: DecidableEq α] : SRefinement (MQ0 α ctx.toBoundedCtx) (MQ1 α ctx) where
  unlift := MQ1.unlift
  lift_unlift := by
    intros mq1 mq0' Hinv Hainv
    simp [FRefinement.lift, MQ1.unlift]
    sorry

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

theorem MQ1.maxPrio_zero [DecidableEq α] (mq : MQ1 α ctx):
  mq.priorities = ∅ → mq.maxPrio = 0 :=
by
  intro Hp
  simp [MQ1.maxPrio]
  simp [Hp]

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

def MQ1.minPrio [DecidableEq α] (mq : MQ1 α ctx) : Prio :=
  Finset.fold min mq.maxPrio id mq.priorities

theorem MQ1.minPrio_zero [DecidableEq α] (mq : MQ1 α ctx):
  mq.priorities = ∅ → mq.minPrio = 0 :=
by
  intro Hps
  have Hmax : mq.maxPrio = 0 := by
    apply maxPrio_zero ; assumption
  simp [MQ1.minPrio]
  simp [Hmax, Hps]

theorem minPrio_le_max_aux (ps : Finset Prio) (df : Prio):
  ps.fold min df id ≤ df :=
by
  induction ps using Finset.induction
  case empty => simp
  case insert p ps Hp Hind =>
    simp
    by_cases p ≤ df
    case pos Hpos =>
      simp [Hpos]
    case neg Hneg =>
      right
      exact Hind

theorem MQ1.minPrio_le_max [DecidableEq α] (mq : MQ1 α ctx):
  mq.minPrio ≤ mq.maxPrio :=
by
  apply minPrio_le_max_aux

theorem minPrio_le_aux (ps : Finset Prio) (df : Prio):
  ∀ p ∈ ps, ps.fold min df id ≤ p :=
by
  induction ps using Finset.induction
  case empty => simp
  case insert q ps Hq Hind =>
    simp
    intros p Hp
    by_cases q ≤ p
    case pos Hpos =>
      simp [Hpos]
    case neg Hneg =>
      right
      exact Hind p Hp

theorem MQ1.minPrio_le [DecidableEq α] (mq : MQ1 α ctx):
  ∀ p ∈ mq.priorities, mq.minPrio ≤ p :=
by
  apply minPrio_le_aux

theorem minPrio_in_aux (ps : Finset Prio) (df : Prio):
  ps.fold min df id ∈ ps ∪ {df} :=
by
  induction ps using Finset.induction
  case empty => simp
  case insert q ps Hq Hind =>
    simp
    simp at Hind
    cases Hind
    case inl Hind =>
      by_cases q ≤ Finset.fold min df (fun x => x) ps
      case pos Hq =>
        left
        exact Hq
      case neg Hq =>
        right
        have Hmin : q ⊓ Finset.fold min df (fun x => x) ps = Finset.fold min df (fun x => x) ps := by
          simp [Hq]
          exact le_of_not_ge Hq
        simp [Hmin]
        left
        exact Hind
    case inr Hind =>
      simp [Hind]
      by_cases q ≤ df
      case pos Hpos =>
        simp [Hpos]
      case neg Hneg =>
        by_cases df ≤ q
        case pos Hpos =>
          simp [Hpos]
        case neg Hneg' =>
          have Htot := le_total q df
          cases Htot
          case inl Htot =>
            simp [Htot]
          case inr Htot =>
            simp [Htot]

theorem MQ1.minPrio_in [DecidableEq α] (mq : MQ1 α ctx):
  mq.minPrio ∈ mq.priorities ∪ {mq.maxPrio} :=
by
  apply minPrio_in_aux

theorem minPrio_in_aux' (ps : Finset Prio) (df : Prio):
  ps ≠ ∅ → ∀ p ∈ ps, p ≤ df → ps.fold min df id ∈ ps :=
by
  have Haux := minPrio_in_aux ps df
  intros Hne p Hp₁ Hp₂
  simp at Haux
  cases Haux
  case inl Haux =>
    simp [Haux]
  case inr Haux =>
    simp [Haux]
    have Hdf := minPrio_le_aux ps df p Hp₁
    simp [Haux] at Hdf
    have Heq: p = df := by
      apply le_antisymm <;> assumption
    simp [←Heq, Hp₁]

theorem MQ1.minPrio_in' [DecidableEq α] (mq : MQ1 α ctx):
  mq.priorities ≠ ∅
  → mq.minPrio ∈ mq.priorities :=
by
  intro Hne
  have Hcut : mq.minPrio ∈ mq.priorities ∪ {mq.maxPrio} := by exact minPrio_in mq
  simp at Hcut
  cases Hcut
  case inl Hin => exact Hin
  case inr Heq =>
    rw [Heq]
    refine maxPrio_in mq ?_
    exact Finset.nonempty_iff_ne_empty.mpr Hne

theorem MQ1.minPrio_empty [DecidableEq α] (mq : MQ1 α ctx):
  mq.priorities = ∅
  → mq.minPrio = mq.maxPrio :=
by
  intro Hne
  have Hcut : mq.minPrio ∈ mq.priorities ∪ {mq.maxPrio} := by exact minPrio_in mq
  simp at Hcut
  cases Hcut
  case inl Hin => simp [Hne] at Hin
  case inr Heq => exact Heq

theorem MQ1.minPrio_min [DecidableEq α] (mq : MQ1 α ctx) :
  ∀ msg ∈ mq.messages, mq.minPrio ≤ msg.prio :=
by
  intros msg Hmsg
  have Hin: msg.prio ∈ mq.priorities := by exact MQ1_prios_in mq msg Hmsg
  exact minPrio_le mq msg.prio Hin

def MQ1.Discard [DecidableEq α] : OrdinaryRNDEvent (MQ0 α ctx.toBoundedCtx) (MQ1 α ctx) Unit (Finset (Message α)) Unit (Finset (Message0 α)) :=
  newRNDEvent MQ0.Discard.toOrdinaryNDEvent {
    lift_in := id
    lift_out ms := Finset.map liftMessage ms
    guard mq _ := mq.messages ≠ ∅
    effect := fun mq _ _ (y, mq') =>
                mq'.clock = mq.clock
                ∧  (∃ ms : Finset (Message α),
                     ms ⊆ mq.messages ∧ ms ≠ ∅ ∧ mq'.messages = mq.messages \ ms
                     ∧ ∀ msg₁ ∈ ms, ∀ msg₂ ∈ mq'.messages, msg₁.prio ≤ msg₂.prio)

    safety := fun mq _ => by
      simp [Machine.invariant]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hgrd mq' Hclk ms Hms₁ Hms₂ Hmq' Hprio
      simp [Hmq'] at Hprio
      simp [Hmq']
      constructor
      · rw [Finset.card_sdiff Hms₁]
        simp [Hinv₁]
        exact Nat.le_add_right_of_le Hinv₁
      constructor
      · simp [Hclk]
        intros msg Hmsg₁ Hmsg₂
        exact Hinv₂ msg Hmsg₁
      constructor
      · intros msg₁ Hmsg₁ Hmsg₁' msg₂ Hmsg₂ Hmsg₂' Hts
        exact Hinv₃ msg₁ Hmsg₁ msg₂ Hmsg₂ Hts
      · intros msg Hmsg Hmsg'
        exact Hinv₄ msg Hmsg

    feasibility := fun mq _ => by
      simp [Machine.invariant]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hgrd
      have Hne : mq.priorities ≠ ∅ := by
        refine Finset.nonempty_iff_ne_empty.mp ?_
        refine Nonempty mq ?_
        exact Finset.nonempty_iff_ne_empty.mpr Hgrd
      have Hex : ∃ msg ∈ mq.messages, msg.prio = mq.minPrio := by
        refine msgEx mq mq.minPrio ?_
        exact minPrio_in' mq Hne
      obtain ⟨msg, Hmsg⟩ := Hex
      exists {mq with messages := mq.messages \ {msg}}
      simp
      obtain ⟨Hmsg₁, Hmsg₁'⟩ := Hmsg
      exists {msg}
      simp [Hmsg₁]
      intros msg₂ Hmsg₂
      intros Hneq
      rw [Hmsg₁']
      exact minPrio_min mq msg₂ Hmsg₂

    strengthening := fun mq _ => by
      simp [Machine.invariant, Refinement.refine, MQ0.Discard, FRefinement.lift]

    simulation := fun mq _ => by
      simp [Machine.invariant, Refinement.refine, MQ0.Discard, FRefinement.lift]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hgrd mq' Hmq' ms Hms₁ Hms₂ Hmq'' Hprio
      constructor
      case left => exact Hmq'
      case right =>
        exists (Finset.map liftMessage ms)
        simp [Hms₁, Hms₂, Hmq'']
        exact
          Finset_map_sdiff mq.messages ms
            { toFun := Message.toMessage0, inj' := liftMessage_inj_ax }
  }

def shiftPrio  [DecidableEq α] (n : Nat) (msg : Message α) : Message α :=
  { msg with prio := msg.prio + (Prio.mk n) }

def shiftPrio' [DecidableEq α] (n : Nat) : Message α ↪ Message α := {
  toFun := shiftPrio n
  inj' := fun m₁ m₂ Heq => by
    simp [shiftPrio] at Heq
    obtain ⟨Heq₁, Heq₂⟩ := Heq
    cases m₁
    case _ x₁ p₁ =>
    cases m₂
    case _ x₂ p₂ =>
      simp at *
      cases p₁
      case mk p₁ =>
      cases p₂
      case mk p₂ =>
        simp
        have Heq₂' : Prio.mk p₁ = Prio.mk p₂ := by
          exact Prio_Add_cancel_left { prio := p₁ } { prio := p₂ } { prio := n } Heq₂
        simp at Heq₂'
        simp [Heq₁, Heq₂']
}

def MQ1.ShiftPrio [DecidableEq α] : OrdinaryRDetEvent (MQ0 α ctx.toBoundedCtx) (MQ1 α ctx) Nat Unit :=
  newConcreteFREvent {
    guard mq n := (MQ1.maxPrio mq) + n ≤ ctx.maxPrio
    action mq n grd :=
      let mq' := { mq with messages := Finset.map (shiftPrio' n) mq.messages }
      ((), mq')

    safety mq n := by
      simp [Machine.invariant, shiftPrio', shiftPrio]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hgrd
      constructor
      · exact Hinv₁
      constructor
      · intros msg Hmsg ; exact Hinv₂ msg Hmsg
      constructor
      · intros msg₁ Hmsg₁ msg₂ Hmsg₂ Hts
        have Heq₁ : msg₁.toMessage0 = msg₂.toMessage0 := by
          exact congrArg Message.toMessage0 (Hinv₃ msg₁ Hmsg₁ msg₂ Hmsg₂ Hts)
        simp [Heq₁]
        have Heq₂ : msg₁.prio = msg₂.prio := by
          exact congrArg Message.prio (Hinv₃ msg₁ Hmsg₁ msg₂ Hmsg₂ Hts)
        exact congrFun (congrArg HAdd.hAdd Heq₂) { prio := n }
      · intros msg Hmsg
        constructor
        · have H₁ : ctx.minPrio ≤ msg.prio := by
            apply (Hinv₄ msg Hmsg).1
          exact Prio_Add_le_left ctx.minPrio msg.prio { prio := n } H₁
        · have H₂ : msg.prio ≤ ctx.maxPrio := by
            apply (Hinv₄ msg Hmsg).2
          have Hp: msg.prio ≤ mq.maxPrio := by
            exact maxPrio_max mq msg Hmsg
          have H₃ : msg.prio + n ≤ mq.maxPrio + n := by
            exact Nat.add_le_add_right Hp n
          exact
            Preorder.le_trans (msg.prio + { prio := n })
              {
                prio :=
                  (match mq.maxPrio with
                    | { prio := p } => p) +
                    n }
              ctx.maxPrio H₃ Hgrd

    simulation mq n := by
      simp [Machine.invariant, FRefinement.lift, shiftPrio', shiftPrio]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hgrd
      sorry

  }


end MQueue
