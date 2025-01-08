import LeanMachinesExamples.MQueue.MQ1

import LeanMachines.Refinement.Functional.NonDet.Basic

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
                  ∧ mq.queue.Nodup
  reset := { queue := [], clock := 0}

theorem MQ2.clock_free [DecidableEq α] (mq : MQ2 α ctx):
  Machine.invariant mq → ∀ x, ∀ p, ⟨⟨x, mq.clock⟩, p⟩ ∉ mq.messages :=
by
  simp [Machine.invariant]
  intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ x p Hin
  have Hinv₂' := Hinv₂ ⟨⟨x, mq.clock⟩, p⟩ Hin
  simp at Hinv₂' -- contradiction

theorem List_Finset_dedup_prop [DecidableEq α] (xs : List α):
  xs.length = xs.toFinset.card
  → xs = xs.dedup :=
by
  intro Hlen
  induction xs
  case nil =>
    simp
  case cons x xs Hind =>
    simp at Hlen
    by_cases x ∈ xs
    case pos Hpos =>
      have Hpos' : x ∈ xs.toFinset := by exact List.mem_toFinset.mpr Hpos
      simp [Hpos'] at Hlen
      simp [Hpos]
      have Hineq: xs.toFinset.card ≤ xs.length := by
        exact List.toFinset_card_le xs
      rw [←Hlen] at Hineq
      have Hcontra: ¬ (xs.length + 1 ≤ xs.length) := by
        exact Nat.not_succ_le_self xs.length
      contradiction
    case neg Hneg =>
      simp [Hneg] at Hlen
      simp [Hneg]
      apply Hind
      · exact Hlen

theorem List_Finset_Nodup_prop [DecidableEq α] (xs : List α):
  xs.length = xs.toFinset.card
  → xs.Nodup :=
by
  intro Hlen
  have Hdedup: xs = xs.dedup := by
    exact List_Finset_dedup_prop xs Hlen
  rw [Hdedup]
  exact List.nodup_dedup xs

theorem List_Nodup_extension [DecidableEq α] (xs : List α):
  xs.Nodup → ∀ x ∈ xs, ∀ y ∈ xs.erase x, y ≠ x :=
by
  intro Hnd
  induction xs
  case nil => simp
  case cons z xs Hind =>
    simp at Hnd
    obtain ⟨Hz, Hnd⟩ := Hnd
    simp [Hnd] at Hind
    intros x Hx y Hy
    by_cases z = x
    case pos Hpos =>
      simp [Hpos] at Hz
      simp [Hpos] at Hy
      exact ne_of_mem_of_not_mem Hy Hz
    case neg Hneg =>
      simp [Hneg] at Hx
      simp [Hneg] at Hy
      cases Hx
      case inl Heq =>
        simp [Heq] at Hneg
      case inr Hneq =>
        cases Hy
        case inl Hy =>
          exact ne_of_eq_of_ne Hy Hneg
        case inr Hy =>
          apply Hind <;> assumption

theorem MQ2.nodup_erase [DecidableEq α] (mq : MQ2 α ctx):
  mq.queue.length = mq.messages.card
  → ∀ msg₁ ∈ mq.queue, ∀ msg₂ ∈ mq.queue.erase msg₁, msg₂ ≠ msg₁ :=
by
  intros Hsize
  have Hnd: mq.queue.Nodup := by exact List_Finset_Nodup_prop mq.queue Hsize
  intros msg₁ Hmsg₁ msg₂ Hmsg₂
  exact List_Nodup_extension mq.queue Hnd msg₁ Hmsg₁ msg₂ Hmsg₂

instance [instDec: DecidableEq α] : FRefinement (MQ1 α ctx) (MQ2 α ctx) where
  lift := MQ2.lift
  lift_safe mq := by
    simp [Machine.invariant]
    intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅
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
  ∧ ctx.minPrio ≤ params.2 ∧ params.2 ≤ ctx.maxPrio

theorem enqueue_guard_strength [DecidableEq α] (mq : MQ2 α ctx) (params : α × Prio):
  enqueue_guard mq params → MQ1.Enqueue.guard mq.lift params :=
by
  simp [MQ1.Enqueue]
  intros Hgrd₁ Hgrd₂ Hgrd₃
  constructor
  · have H : mq.queue.toFinset.card ≤ mq.queue.length := by
      exact List.toFinset_card_le mq.queue
    exact Nat.lt_of_le_of_lt H Hgrd₁
  · exact ⟨Hgrd₂, Hgrd₃⟩

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
  simp [Finset.insert_eq, Finset.union_comm]


def MQ2.Enqueue [DecidableEq α]: OrdinaryREvent (MQ1 α ctx) (MQ2 α ctx) (α × Prio) Unit :=
  newFREvent' MQ1.Enqueue.toOrdinaryEvent {
    guard := fun mq (x, px) => mq.queue.length < ctx.maxCount
                               ∧ ctx.minPrio ≤ px ∧ px ≤ ctx.maxPrio

    action := fun mq (x, px) =>
                { queue := ⟨⟨x, mq.clock⟩, px⟩ :: mq.queue,
                  clock := mq.clock + 1 }

    safety := fun mq (x, px) => by
      intro Hinv
      have Hclk := MQ2.clock_free mq Hinv
      revert Hinv
      simp [Machine.invariant]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hgrd₁ Hgrd₂ Hgrd₃
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
        have Hclk' := Hclk msg.payload msg.prio
        simp [Hts] at Hclk'
        contradiction
      · intros msg Hmsg
        constructor
        · intro Hts
          have Hclk' := Hclk msg.payload msg.prio
          simp [←Hts] at Hclk'
          have Hmsg' : msg ∈ mq.messages := by exact in_queue_in_messages mq msg Hmsg
          contradiction
        · intros msg' Hmsg' Hts
          exact Hinv₃ msg Hmsg msg' Hmsg' Hts
      constructor
      constructor
      · exact ⟨Hgrd₂, Hgrd₃⟩
      · intros msg Hmsg
        exact Hinv₄ msg Hmsg
      · simp [Hinv₅]
        intro Hcontra
        have Hinv₂' := Hinv₂ { payload := x, timestamp := mq.clock, prio := px } Hcontra
        simp at Hinv₂'

    lift_in := fun (x, px) => (x, px)

    strengthening := fun mq (x, px) => by
      simp [Machine.invariant, MQ1.Enqueue, FRefinement.lift]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hgrd₁ Hgrd₂ Hgrd₃
      constructor
      · have H : mq.queue.toFinset.card ≤ mq.queue.length := by
          exact List.toFinset_card_le mq.queue
        exact Nat.lt_of_le_of_lt H Hgrd₁
      · exact ⟨Hgrd₂, Hgrd₃⟩

    simulation := fun mq (x, px) => by
      intro Hinv
      simp
      intros Hgrd₁ Hgrd₂ Hgrd₃
      have Hlift : FRefinement.lift mq = mq.lift := by
        rfl
      rw [Hlift]
      rw [←@enqueue_action_prop (mq:=mq) (params:=(x, px))]
      exact rfl
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

theorem Finset_sdiff_new_elem [DecidableEq α] (x x' : α) (s : Finset α):
  x ≠ x' → x' ∈ s \ {x} → x' ∈ s :=
by
  intros Hneq Hx'
  by_cases x' ∈ s
  case pos Hpos =>
    exact Hpos
  case neg Hneg =>
    have Hcontra: x' ∉ s \ {x} := by
      exact Finset.not_mem_sdiff_of_not_mem_left Hneg
    contradiction

theorem Finset_sdiff_elem [DecidableEq α] (x x' : α) (s : Finset α):
  x' ∈ s → x' ∉ s \ {x} → x' = x :=
by
  intros Hx'₁ Hx'₂
  by_cases x' = x
  case pos Hpos =>
    exact Hpos
  case neg Hneg =>
    have Hcontra: x' ∈ s \ {x} := by
      simp [Hx'₁, Hneg]
    contradiction

theorem Finset_sdiff_neq [DecidableEq α] (x x' : α) (s : Finset α):
  x' ∈ s \ {x} → x' ≠ x :=
by
  intros Hx' Hneq
  simp [Hneq] at Hx'

theorem List_erase_in_prop [DecidableEq α] (xs : List α) (y : α):
  ∀ x ∈ xs, x ∉ (xs.erase y) → x = y :=
by
  induction xs
  case nil => simp
  case cons z xs Hind =>
    simp
    constructor
    · intro Hz
      simp [List.erase_cons] at Hz
      by_cases z = y
      case pos Hpos =>
        assumption
      case neg Hneg =>
        simp [Hneg] at Hz
    · intros a Ha
      intro Ha'
      apply Hind
      · assumption
      · simp [List.erase_cons] at Ha'
        by_cases z = y
        case pos Hpos =>
          simp [Hpos] at Ha'
          contradiction
        case neg Hneg =>
          simp [Hneg] at Ha'
          simp [Ha']

theorem List_nodup_erase_diff_prop [DecidableEq α] (xs : List α) (y : α):
  xs.Nodup → x ∈ (xs.erase y) → x ≠ y :=
by
  intro Hnd Hx
  intro Heq
  rw [←Heq] at Hx
  have Hcontra: x ∉ xs.erase x := by
    exact List.Nodup.not_mem_erase Hnd
  contradiction

theorem List_erase_mem [DecidableEq α] (xs : List α) (y : α):
  ∀ x ∈ xs.erase y, x ≠ y → x ∈ xs :=
by
  intros x Hx Hxy
  exact (List.mem_erase_of_ne Hxy).mp Hx

theorem Finset_sdiff_singleton_eq_self.{u_1} {α : Type u_1} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s):
  s \ {a} = s :=
by
  simp [ha]

theorem List_erase_Finset_Nodup [DecidableEq α] (xs : List α) (y : α):
  xs.Nodup → (xs.erase y).toFinset = xs.toFinset \ {y} :=
by
  induction xs
  case nil =>
    simp
  case cons x xs Hind =>
    simp [List.erase_cons]
    intros Hx Hnd
    split
    case isTrue Heq =>
      rw [←Heq]
      rw [←Heq] at Hind
      rw [Finset.insert_sdiff_of_mem xs.toFinset (List.Mem.head [])]
      have Hx' : x ∉ xs.toFinset := by
        rw [@List.mem_toFinset]
        exact Hx
      exact Eq.symm (Finset_sdiff_singleton_eq_self Hx')
    case isFalse Hneq =>
      simp [Hneq]
      rw [Hind Hnd]
      refine Eq.symm (Finset.insert_sdiff_of_not_mem xs.toFinset ?_)
      simp [Finset.sdiff_singleton_eq_erase]
      assumption

def MQ2.Dequeue [DecidableEq α] : OrdinaryRNDEvent (MQ1 α ctx) (MQ2 α ctx) Unit (α × Prio) :=
  newFRNDEvent MQ1.Dequeue.toOrdinaryNDEvent {
    lift_in := id
    lift_out := id
    guard (mq : MQ2 α ctx) _ := mq.queue ≠ []
    effect := fun mq _ ((y, py), mq') =>
                ∃ msg ∈ mq.queue, y = msg.payload ∧ py = msg.prio
                                     ∧ mq'.queue = mq.queue.erase msg
                                     ∧ mq'.clock = mq.clock
                                     ∧ ∀ msg' ∈ mq.queue, msg' ≠ msg → msg'.prio ≤ msg.prio

    safety mq _ := by
      simp [Machine.invariant]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hgrd y py mq' msg Hmsg Hy Hpy Hmq' Hclk Hprio

      have HmsgLemma : ∀ msg' ∈ mq.queue, msg' ∉ mq'.queue → msg' = msg := by
        rw [Hmq']
        apply List_erase_in_prop

      have HmsgLemma₂ : ∀ msg' ∈ mq'.queue, msg' ≠ msg := by
        rw [Hmq']
        intros msg' Hmsg'
        exact List_Nodup_extension mq.queue Hinv₅ msg Hmsg msg' Hmsg'

      have HmsgLemma₃ : ∀ msg' ∈ mq'.queue, msg' ≠ msg → msg' ∈ mq.queue := by
        rw [Hmq']
        intros msg' Hmsg' Hneq
        exact List_erase_mem mq.queue msg msg' Hmsg' Hneq

      constructor
      · simp [Hmq']
        rw [@List.length_erase]
        simp [Hmsg]
        exact Nat.le_add_right_of_le Hinv₁
      constructor
      · intros msg' Hmsg'
        have Hneq: msg' ≠ msg := by
          exact HmsgLemma₂ msg' Hmsg'
        have Hmsg'' : msg' ∈ mq.queue := by
          exact HmsgLemma₃ msg' Hmsg' (HmsgLemma₂ msg' Hmsg')
        rw [Hclk]
        exact Hinv₂ msg' Hmsg''
      constructor
      · intros msg₁ Hmsg₁ msg₂ Hmsg₂ Hts
        have Hmsg₁' : msg₁ ≠ msg := by
          exact HmsgLemma₂ msg₁ Hmsg₁
        have Hmsg₂' : msg₂ ≠ msg := by
          exact HmsgLemma₂ msg₂ Hmsg₂
        have Hmsg₁'' : msg₁ ∈ mq.queue := by exact HmsgLemma₃ msg₁ Hmsg₁ (HmsgLemma₂ msg₁ Hmsg₁)
        have Hmsg₂'' : msg₂ ∈ mq.queue := by exact HmsgLemma₃ msg₂ Hmsg₂ (HmsgLemma₂ msg₂ Hmsg₂)
        exact Hinv₃ msg₁ Hmsg₁'' msg₂ Hmsg₂'' Hts
      constructor
      · intros msg' Hmsg'
        by_cases msg' ∈ mq.queue
        case pos Hpos =>
          exact Hinv₄ msg' (HmsgLemma₃ msg' Hmsg' (HmsgLemma₂ msg' Hmsg'))
        case neg Hneg =>
          have Heq : msg' = msg := by exact False.elim (Hneg (HmsgLemma₃ msg' Hmsg' (HmsgLemma₂ msg' Hmsg')))
          exact Hinv₄ msg' (HmsgLemma₃ msg' Hmsg' (HmsgLemma₂ msg' Hmsg'))
      · rw [Hmq']
        exact List.Nodup.erase msg Hinv₅

    feasibility mq x := by
      intro Hinv
      simp
      intro Hnempty
      have Hainv := FRefinement.lift_safe (AM:=MQ1 α ctx) (M:=MQ2 α ctx) mq Hinv
      have Hafeqs_ := MQ1.Dequeue.po.feasibility (m:=mq.lift) () Hainv
      simp [MQ1.Dequeue, FRefinement.lift] at *
      obtain ⟨pl, p, mq', msg, Hmsg, Hpl, Hp, Hmq', Hprio⟩ := Hafeqs_ Hnempty ; clear Hafeqs_
      exists pl ; exists p
      exists {mq with queue := mq.queue.erase msg}
      exists msg

    strengthening mq _ := by
      simp [Machine.invariant, Refinement.refine, MQ1.Dequeue, FRefinement.lift]

    simulation mq _ := by
      simp [Machine.invariant, Refinement.refine, MQ1.Dequeue, FRefinement.lift]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hgrd y py mq' msg Hmsg Hy Hpy Hmq' Hclk Hprio
      simp [Hmq']
      exists msg
      simp [Hmsg, Hy, Hpy, Hclk]
      constructor
      · exact List_erase_Finset_Nodup mq.queue msg Hinv₅
      · intros msg Hmsg Hneq
        exact Hprio msg Hmsg Hneq

  }

end MQueue
