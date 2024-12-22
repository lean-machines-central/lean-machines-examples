import LeanMachinesExamples.MQueue.MQ1

namespace MQueue

open Bounded
open Prioritized
open Clocked

structure MQ2 (α : Type 0) [instDec: DecidableEq α] (ctx : MQContext)
    extends Clocked where
  queue : List (Message α)

@[simp]
def MQ2.messages [DecidableEq α] (mq : MQ2 α ctx) : Finset (Message α) :=
  mq.queue.toFinset

theorem in_queue_in_messages [DecidableEq α] (mq : MQ2 α ctx):
  ∀ msg ∈ mq.queue, msg ∈ mq.messages :=
by
  simp

theorem in_messages_in_queue [DecidableEq α] (mq : MQ2 α ctx):
  ∀ msg ∈ mq.messages, msg ∈ mq.queue :=
by
  simp

@[simp]
def MQ2.lift [DecidableEq α] (mq : MQ2 α ctx) : MQ1 α ctx :=
  {clock := mq.clock, messages := mq.messages}

theorem lift_Messages [DecidableEq α] (mq : MQ2 α ctx):
  mq.lift.messages = mq.messages :=
by
  simp

instance [instDec: DecidableEq α]: Machine MQContext (MQ2 α (instDec:=instDec) ctx) where
  context := ctx
  invariant mq := mq.queue.length ≤ ctx.maxCount
                  ∧ (∀ msg ∈ mq.queue, msg.timestamp < mq.clock)
                  ∧ (∀ msg₁ ∈ mq.queue, ∀ msg₂ ∈ mq.queue, msg₁.timestamp = msg₂.timestamp → msg₁ = msg₂)
                  ∧ (∀ msg ∈ mq.queue, ctx.minPrio ≤ msg.prio ∧ msg.prio ≤ ctx.maxPrio)
  reset := { queue := [], clock := 0}

instance [instDec: DecidableEq α] : FRefinement (MQ1 α ctx) (MQ2 α ctx) where
  lift := MQ2.lift
  lift_safe mq := by
    simp [Machine.invariant]
    intros Hinv₁ Hinv₂ Hinv₃ Hinv₄
    constructor
    · have H : mq.queue.toFinset.card ≤ mq.queue.length := by
        exact List.toFinset_card_le mq.queue
      exact Nat.le_trans H Hinv₁
    constructor
    · intros msg Hmsg ; exact Hinv₂ msg Hmsg
    constructor
    · intros msg₁ Hmsg₁ msg₂ Hmsg₂ Hts
      exact Hinv₃ msg₁ Hmsg₁ msg₂ Hmsg₂ Hts
    · intros msg Hmsg
      exact Hinv₄ msg Hmsg

def MQ2.Init [instDec: DecidableEq α] : InitREvent (MQ1 α ctx) (MQ2 α ctx) Unit Unit :=
  newInitREvent'' MQ1.Init.toInitEvent {
    init := { queue := [], clock := 0}
    safety _ := by simp [Machine.invariant]
    strengthening _ := by simp [Machine.invariant, MQ1.Init]
    simulation _ := by simp [Machine.invariant, Refinement.refine, MQ1.Init, FRefinement.lift]
  }

@[local simp]
def enqueue_guard [DecidableEq α] (mq : MQ2 α ctx) (params : α × Prio) : Prop :=
  mq.queue.length < ctx.maxCount
  ∧ (∀ msg ∈ mq.queue, msg.timestamp ≠ mq.clock)
  ∧ ctx.minPrio ≤ params.2 ∧ params.2 ≤ ctx.maxPrio

theorem enqueue_guard_strength [DecidableEq α] (mq : MQ2 α ctx) (params : α × Prio):
  enqueue_guard mq params → MQ1.Enqueue.guard mq.lift params :=
by
  simp [MQ1.Enqueue]
  intros Hgrd₁ Hgrd₂ Hgrd₃ Hgrd₄
  constructor
  · have H : mq.queue.toFinset.card ≤ mq.queue.length := by
      exact List.toFinset_card_le mq.queue
    exact Nat.lt_of_le_of_lt H Hgrd₁
  constructor
  · intros msg Hmsg
    exact Hgrd₂ msg Hmsg
  · exact ⟨Hgrd₃, Hgrd₄⟩


@[local simp]
def enqueue_action [DecidableEq α] (mq : MQ2 α ctx) (params : α × Prio) : MQ2 α ctx :=
  { queue := ⟨⟨params.1, mq.clock⟩, params.2⟩ :: mq.queue,
                  clock := mq.clock + 1 }

theorem enqueue_action_prop [DecidableEq α] (mq : MQ2 α ctx) (params : α × Prio):
  (enqueue_action mq params).lift = ((MQ1.Enqueue.to_Event).action mq.lift params).2 :=
by
  simp [MQ1.Enqueue]
  have Hre : mq.queue.toFinset = mq.messages := by
    exact rfl

  rw [Hre, ←lift_Messages]
  -- Reuse from MQ1
  sorry


def MQ2.Enqueue [DecidableEq α] : OrdinaryREvent (MQ1 α ctx) (MQ2 α ctx) (α × Prio) Unit :=
  newFREvent' MQ1.Enqueue.toOrdinaryEvent {
    guard := fun mq (x, px) => mq.queue.length < ctx.maxCount
                               ∧ (∀ msg ∈ mq.queue, msg.timestamp ≠ mq.clock)
                               ∧ ctx.minPrio ≤ px ∧ px ≤ ctx.maxPrio

    action := fun mq (x, px) =>
                { queue := ⟨⟨x, mq.clock⟩, px⟩ :: mq.queue,
                  clock := mq.clock + 1 }

    safety := fun mq (x, px) => by
      simp [Machine.invariant]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hgrd₁ Hgrd₂ Hgrd₃ Hgrd₄
      constructor
      · exact Hgrd₁
      constructor
      constructor
      · refine Clock_LT mq.clock (mq.clock + 1) ?_
        exact Nat.lt_add_one mq.clock.val
      · intros msg Hmsg
        have Hinv₂' := Hinv₂ msg Hmsg
        refine Clock_LT msg.timestamp (mq.clock + 1) ?_
        apply Clock_LT_conv at Hinv₂'
        exact Nat.lt_succ_of_lt (Hinv₂ msg Hmsg)
      constructor
      constructor
      · intros msg Hmsg Hts
        exact False.elim (Hgrd₂ msg Hmsg (id (Eq.symm Hts)))
      · intros msg Hmsg
        constructor
        · intro Hts
          exact False.elim (Hgrd₂ msg Hmsg Hts)
        · intros msg' Hmsg' Hts
          exact Hinv₃ msg Hmsg msg' Hmsg' Hts
      · constructor
        · exact ⟨Hgrd₃, Hgrd₄⟩
        · intros msg Hmsg
          exact Hinv₄ msg Hmsg

    lift_in := fun (x, px) => (x, px)

    strengthening := fun mq (x, px) => by
      simp [Machine.invariant, MQ1.Enqueue, FRefinement.lift]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hgrd₁ Hgrd₂ Hgrd₃ Hgrd₄
      constructor
      · have H : mq.queue.toFinset.card ≤ mq.queue.length := by
          exact List.toFinset_card_le mq.queue
        exact Nat.lt_of_le_of_lt H Hgrd₁
      constructor
      · intros msg Hmsg
        exact Hgrd₂ msg Hmsg
      · exact ⟨Hgrd₃, Hgrd₄⟩

    simulation := fun mq (x, px) => by
      intro Hinv
      have Hainv := FRefinement.lift_safe mq.lift Hinv
      simp [Machine.invariant, MQ1.Enqueue, FRefinement.lift]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hgrd₁ Hgrd₂ Hgrd₃ Hgrd₄
      have Hlift := lift_Messages mq
      unfold MQ2.messages at Hlift
      rw [←Hlift]
      have Hasim := MQ1.Enqueue.po.simulation mq.lift (x, px)
  }

def MQ2.priorities [DecidableEq α] (mq : MQ2 α ctx) : Finset Prio :=
  mq.queue.foldl (fun ps msg => ps ∪ {msg.prio}) ∅

theorem List_Finset_foldl_init [DecidableEq α] (xs: List α):
  ∀ s : Finset α, List.foldl (fun t e => t ∪ {e}) s xs = s ∪ (List.foldl (fun t e => t ∪ {e}) ∅ xs) :=
by
  induction xs
  case nil => simp
  case cons x xs Hind =>
    intro s
    simp
    rw [Hind]
    rw [@Finset.union_assoc]
    rw [← Hind]

theorem List_Finset_foldl_map_init [DecidableEq α] [DecidableEq β] (xs: List α) (f : α → β):
  ∀ s : Finset β, List.foldl (fun t e => t ∪ {f e}) s xs = s ∪ (List.foldl (fun t e => t ∪ {f e}) ∅ xs) :=
by
  induction xs
  case nil => simp
  case cons x xs Hind =>
    intro s
    simp
    rw [Hind]
    rw [@Finset.union_assoc]
    rw [← Hind]

theorem lift_Prios [DecidableEq α] (mq : MQ2 α ctx):
  mq.lift.priorities = mq.priorities :=
by
  simp [MQ1.priorities, MQ2.priorities]
  induction mq.queue
  case nil => simp
  case cons msg queue Hind =>
    simp
    rw [Hind]
    rw [← @List_Finset_foldl_map_init]

theorem MQ2_prios_in [DecidableEq α] (mq : MQ2 α ctx):
  ∀ msg ∈ mq.messages, msg.prio ∈ mq.priorities :=
by
  have H := MQ1_prios_in mq.lift
  rw [lift_Messages,lift_Prios] at H
  exact H

def MQ2.maxPrio [DecidableEq α] (mq : MQ2 α ctx) : Prio :=
  mq.lift.maxPrio

theorem MQ2.maxPrio_max [DecidableEq α] (mq : MQ2 α ctx) :
  ∀ msg ∈ mq.queue, msg.prio ≤ mq.maxPrio :=
by
  intros msg Hmsg
  have Hmsg' : msg ∈ mq.messages := by exact in_queue_in_messages mq msg Hmsg
  rw [←lift_Messages] at Hmsg'
  apply MQ1.maxPrio_max ; assumption

theorem MQ2.maxPrio_in [DecidableEq α] (mq : MQ2 α ctx):
  Finset.Nonempty mq.priorities
  → mq.maxPrio ∈ mq.priorities :=
by
  rw [← @lift_Prios]
  apply MQ1.maxPrio_in

theorem MQ2.msgEx [DecidableEq α] (mq : MQ2 α ctx):
  ∀ prio ∈ mq.priorities, ∃ msg ∈ mq.messages, msg.prio = prio :=
by
  rw [← @lift_Prios, ← @lift_Messages]
  apply MQ1.msgEx mq.lift

def MQ2.maxElemEx [DecidableEq α] (mq : MQ2 α ctx):
  mq.queue ≠ []
  → ∃ msg ∈ mq.queue, msg.prio = mq.maxPrio :=
by
  intro Hne
  have Hne' : Finset.Nonempty mq.messages := by
    simp
    exact Hne
  have Hlift := MQ1.maxElemEx mq.lift
  rw [lift_Messages] at Hlift
  have Hlift' := Hlift Hne'
  obtain ⟨msg, Hmsg, Hprio⟩ := Hlift'
  exists msg
  constructor
  · exact in_messages_in_queue mq msg Hmsg
  · exact Hprio

def MQ1.Dequeue [DecidableEq α] : OrdinaryRNDEvent (MQ0 α ctx.toBoundedCtx) (MQ1 α ctx) Unit (α × Prio) Unit α :=
  newRNDEvent MQ0.Dequeue.toOrdinaryNDEvent {
    lift_in := id
    lift_out := fun (x, _) => x
    guard mq _ := mq.messages ≠ ∅
    effect := fun mq _ ((y, py), mq') =>
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
