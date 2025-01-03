import LeanMachinesExamples.MQueue.MQ2

import LeanMachines.Refinement.Strong.Basic

namespace MQueue

open Bounded
open Prioritized
open Clocked

instance [DecidableEq α]: LT (Message α) where
  lt m₁ m₂ := (m₁.prio < m₂.prio)
              ∨ (m₁.prio = m₂.prio ∧ m₁.timestamp < m₂.timestamp)

theorem Message_lift_lt_prio [DecidableEq α] (m₁ m₂ : Message α):
  m₁.prio < m₂.prio
  → m₁ < m₂ :=
by
  intro H
  -- unfold LT.lt at *
  left
  exact H

theorem Message_lift_lt_ts [DecidableEq α] (m₁ m₂ : Message α):
  m₁.prio = m₂.prio
  → m₁.timestamp < m₂.timestamp
  → m₁ < m₂ :=
by
  intro Hp Hts
  --unfold LT.lt at *
  right
  exact ⟨Hp, Hts⟩

theorem Message_lt_trans [DecidableEq α] (m₁ m₂ m₃ : Message α):
  m₁ < m₂ → m₂ < m₃
  → m₁ < m₃ :=
by
  intros H₁ H₂
  unfold LT.lt at *
  simp [instLTMessage] at *
  cases H₁
  case inl H₁ =>
    cases H₂
    case inl H₂ =>
      left
      apply lt_trans H₁ H₂
    case inr H₂ =>
      simp [H₂] at H₁
      left
      assumption
  case inr H₁ =>
    cases H₂
    case inl H₂ =>
      obtain ⟨H₁, H₁'⟩ := H₁
      rw [←H₁] at H₂
      left
      assumption
    case inr H₂ =>
      right
      obtain ⟨H₁, H₁'⟩ := H₁
      obtain ⟨H₂, H₂'⟩ := H₂
      simp [H₁,H₂]
      apply lt_trans H₁' H₂'

instance [DecidableEq α]: LE (Message α) where
  le m₁ m₂ := m₁ < m₂ ∨ m₁ = m₂

instance [DecidableEq α]: Preorder (Message α) where
  le_refl m := by simp [LE.le]

  le_trans m₁ m₂ m₃ := by
    simp [LE.le]
    intros H₁ H₂
    cases H₁
    case inl H₁ =>
      cases H₂
      case inl H₂ =>
        left
        exact Message_lt_trans m₁ m₂ m₃ H₁ H₂
      case inr H₂ =>
        left
        exact lt_of_lt_of_eq H₁ H₂
    case inr H₁ =>
      cases H₂
      case inl H₂ =>
        left
        exact lt_of_eq_of_lt H₁ H₂
      case inr H₂ =>
        right
        simp [H₁, H₂]

  lt_iff_le_not_le m₁ m₂ := by
    simp [LE.le]
    constructor
    case mp =>
      intro H
      constructor
      · left ; assumption
      · constructor
        · intro H'
          unfold LT.lt at *
          simp [instLTMessage] at *
          cases H
          case _ H =>
            cases H'
            case _ H' =>
              have H'' : ¬ (m₂.prio < m₁.prio) := by
                exact not_lt_of_gt H
              contradiction
            case _ H' =>
              simp [H'] at H
          case _ H =>
            obtain ⟨H₁,H₂⟩ := H
            cases H'
            case _ H' =>
              rw [←H₁] at H'
              exact (lt_self_iff_false m₁.prio).mp H'
            case _ H' =>
              simp [H₁] at H'
              have H'' : ¬ (m₂.timestamp < m₁.timestamp) := by
                exact not_lt_of_gt H₂
              contradiction
        · intro Heq
          rw [Heq] at H
          unfold LT.lt at H
          simp [instLTMessage] at H
    case mpr =>
      intro ⟨H₁, H₂, H₃⟩
      cases H₁
      case inl H₁ =>
        assumption
      case inr H₁ =>
        exact False.elim (H₃ (id (Eq.symm H₁)))

instance [DecidableEq α]: PartialOrder (Message α) where
  le_antisymm m₁ m₂ := by
    intros H₁ H₂
    simp [LE.le] at *
    cases H₁
    case inl H₁ =>
      cases H₂
      case inl H₂ =>
        unfold LT.lt at *
        simp [instLTMessage] at *
        cases H₁
        case inl H₁ =>
          cases H₂
          case inl H₂ =>
            have Hcontra: ¬ (m₁.prio < m₂.prio) := by
              exact not_lt_of_gt H₂
            contradiction
          case inr H₂ =>
            simp [H₂.1] at H₁
        case inr H₁ =>
          obtain ⟨H₁,H₁'⟩ := H₁
          cases H₂
          case _ H₂ =>
            simp [H₁] at H₂
          case _ H₂ =>
            simp [H₁] at H₂
            have Hcontra: ¬ (m₂.timestamp < m₁.timestamp) := by
              exact not_lt_of_gt H₁'
            contradiction
      case inr H₂ =>
        simp [H₂]
    case inr H₁ =>
      simp [H₁]

-- Remark : messages do not form a linear order since payload are not observed
-- (the order is not total)

instance Message.instDecidableLT [DecidableEq α] : DecidableRel (α := Message α) (·<·) :=
  fun m₁ m₂ ↦  by
    simp
    unfold LT.lt
    simp [instLTMessage]
    exact instDecidableOr

instance Message.instDecidableLE [DecidableEq α] : DecidableRel (α := Message α) (·≤·) :=
  fun m₁ m₂ ↦  by simp [LE.le]
                  exact instDecidableOr

structure MQ3 (α : Type 0) [instDec: DecidableEq α] (ctx : MQContext)
    extends MQ2 α ctx where

@[simp]
def MQ3.lift [DecidableEq α] (mq : MQ3 α ctx) : MQ2 α ctx :=
  mq.toMQ2

@[simp]
def MQ3.unlift [DecidableEq α] (_ : MQ3 α ctx) (amq' : MQ2 α ctx) : MQ3 α ctx :=
  { queue := amq'.queue.insertionSort (·≤·), clock := amq'.clock }

instance [instDec: DecidableEq α]: Machine MQContext (MQ3 α (instDec:=instDec) ctx) where
  context := ctx
  invariant mq := mq.queue.length ≤ ctx.maxCount
                  ∧ (∀ msg ∈ mq.queue, msg.timestamp < mq.clock)
                  ∧ (∀ msg₁ ∈ mq.queue, ∀ msg₂ ∈ mq.queue, msg₁.timestamp = msg₂.timestamp → msg₁ = msg₂)
                  ∧ (∀ msg ∈ mq.queue, ctx.minPrio ≤ msg.prio ∧ msg.prio ≤ ctx.maxPrio)
                  ∧ mq.queue.Nodup
                  ∧ mq.queue.Sorted (·≤·)
  reset := { queue := [], clock := 0}

theorem MQ3.clock_free [DecidableEq α] (mq : MQ3 α ctx):
  Machine.invariant mq → ∀ x, ∀ p, ⟨⟨x, mq.clock⟩, p⟩ ∉ mq.messages :=
by
  simp [Machine.invariant]
  intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv₆ x p Hin
  have Hinv₂' := Hinv₂ ⟨⟨x, mq.clock⟩, p⟩ Hin
  simp at Hinv₂' -- contradiction

/- Remark : Strong refinement is not possible because equality of
abstract state is too strong a requirement
(one cannot recover the initial - arbibrary - ordering of the
abstract event queue).
-/
instance [instDec: DecidableEq α] : FRefinement (MQ2 α ctx) (MQ3 α ctx) where
  lift := MQ3.lift
  lift_safe mq := by
    simp [Machine.invariant]
    intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv₆
    simp [*]
    constructor
    · apply Hinv₂
    constructor
    · apply Hinv₃
    · apply Hinv₄


def MQ3.Init [instDec: DecidableEq α] : InitREvent (MQ2 α ctx) (MQ3 α ctx) Unit Unit :=
  newInitREvent'' MQ2.Init.toInitEvent {
    init := { queue := [], clock := 0}
    safety _ := by simp [Machine.invariant]
    strengthening _ := by simp [Machine.invariant, MQ2.Init]
    simulation _ := by simp [Machine.invariant, Refinement.refine, MQ2.Init, FRefinement.lift]
  }

@[local simp]
def MQ3.enqueue_guard [DecidableEq α] (mq : MQ3 α ctx) (params : α × Prio) : Prop :=
  mq.queue.length < ctx.maxCount
  ∧ ctx.minPrio ≤ params.2 ∧ params.2 ≤ ctx.maxPrio

theorem MQ3.enqueue_guard_strength [DecidableEq α] (mq : MQ3 α ctx) (params : α × Prio):
  MQ3.enqueue_guard mq params → MQ2.Enqueue.guard mq.lift params :=
by
  simp [MQ2.Enqueue, MQ3.enqueue_guard]

@[local simp]
def MQ3.enqueue_action [DecidableEq α] (mq : MQ3 α ctx) (params : α × Prio) : MQ3 α ctx :=
  { queue := mq.queue.orderedInsert (·≤·) ⟨⟨params.1, mq.clock⟩, params.2⟩,
                  clock := mq.clock + 1 }

def MQ3.Enqueue [DecidableEq α]: OrdinaryREvent (MQ2 α ctx) (MQ3 α ctx) (α × Prio) Unit :=
  newFREvent' MQ2.Enqueue.toOrdinaryEvent {
    guard := MQ3.enqueue_guard

    action := MQ3.enqueue_action

    safety := fun mq (x, px) => by
      intro Hinv
      have Hclk := MQ3.clock_free mq Hinv
      revert Hinv
      simp [Machine.invariant, MQ3.enqueue_guard, MQ3.enqueue_action]
      intro Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv₆ Hgrd₁ Hgrd₂ Hgrd₃
      constructor
      · simp [@List.orderedInsert_length]
        exact Hgrd₁
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
        simp [Hts]
        have Hclk' := Hclk msg.payload msg.prio
        simp [Hts] at Hclk'
        contradiction
      · intros msg Hmsg
        constructor
        · intro Hts
          simp [←Hts]
          have Hclk' := Hclk msg.payload msg.prio
          simp [←Hts] at Hclk'
          contradiction
        · intros msg' Hmsg' Hts
          exact Hinv₃ msg Hmsg msg' Hmsg' Hts
      constructor
      constructor
      · exact ⟨Hgrd₂, Hgrd₃⟩
      · intros msg Hmsg
        exact Hinv₄ msg Hmsg
      constructor
      · sorry   -- need a result about  orderedInsert vs. NoDup
      · refine
        List.Sorted.orderedInsert { payload := x, timestamp := mq.clock, prio := px } mq.queue Hinv₆

        simp [Hinv₆]
        intro Hcontra
        have Hinv₂' := Hinv₂ { payload := x, timestamp := mq.clock, prio := px } Hcontra
        simp at Hinv₂'
        exact Hgrd₂ { payload := x, timestamp := mq.clock, prio := px } Hcontra rfl

    lift_in := fun (x, px) => (x, px)

    strengthening := fun mq (x, px) => by
      simp [Machine.invariant, MQ1.Enqueue, FRefinement.lift]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hgrd₁ Hgrd₂ Hgrd₃ Hgrd₄
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
      simp
      intros Hgrd₁ Hgrd₂ Hgrd₃ Hgrd₄
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
