import LeanMachinesExamples.MQueue.MQ2

import LeanMachines.Refinement.Strong.Basic

namespace MQueue

open Bounded
open Prioritized
open Clocked

abbrev MessageSig := Prio × Clock

def Message.sig [DecidableEq α] (msg : Message α) : MessageSig := (msg.prio, msg.timestamp)

instance: LT MessageSig where
  lt := fun (p₁,c₁) (p₂,c₂) => (p₁ < p₂) ∨ (p₁ = p₂ ∧ c₁ < c₂)

instance: DecidableRel (α:=MessageSig) (·<·) :=
  fun (p₁, c₁) (p₂, c₂) => by
    simp
    unfold LT.lt
    simp [instLTMessageSig]
    exact instDecidableOr

example: ((Prio.mk 2, Clock.mk 3) : MessageSig) < (Prio.mk 3, Clock.mk 2) := by
  unfold LT.lt
  simp [instLTMessageSig]

example: decide (((Prio.mk 2, Clock.mk 3) : MessageSig) < (Prio.mk 3, Clock.mk 2)) = true := rfl

theorem MessageSig_lt_prio (m₁ m₂ : MessageSig):
  m₁.1 < m₂.1 → m₁ < m₂ :=
by
  intro Hlt
  unfold LT.lt
  simp [instLTMessageSig]
  left
  assumption

theorem MessageSig_lt_clk (m₁ m₂ : MessageSig):
  m₁.1 = m₂.1
  → m₁.2 < m₂.2
  → m₁ < m₂ :=
by
  intros Hple Hclt
  unfold LT.lt
  simp [instLTMessageSig]
  right
  exact ⟨Hple, Hclt⟩


instance: LE MessageSig where
  le := fun m₁ m₂ => (m₁ < m₂) ∨ (m₁ = m₂)

example: ((Prio.mk 2, Clock.mk 3) : MessageSig) ≤ (Prio.mk 3, Clock.mk 2) := by
  simp [LE.le]
  unfold LT.lt
  simp [instLTMessageSig]

instance: DecidableRel (α:=MessageSig) (·≤·) :=
  fun (p₁, c₁) (p₂, c₂) => by
    simp
    unfold LE.le
    simp [instLEMessageSig]
    exact instDecidableOr

instance: Preorder MessageSig where
  le_refl m := by
    unfold LE.le
    simp [instLEMessageSig]

  le_trans m₁ m₂ m₃ := by
    cases m₁
    case mk p₁ c₁ =>
    cases m₂
    case mk p₂ c₂ =>
    cases m₃
    case mk p₃ c₃ =>
      intros H₁ H₂
      unfold LE.le at *
      simp [instLEMessageSig] at *
      cases H₁
      case inl Hlt₁ =>
        cases H₂
        case inl Hlt₂ =>
          left
          unfold LT.lt at *
          simp [instLTMessageSig] at *
          cases Hlt₁
          case inl Hlt₁ =>
            cases Hlt₂
            case inl Hlt₂ =>
              left
              exact lt_trans Hlt₁ Hlt₂
            case inr Heq₂ =>
              left
              simp [Heq₂] at Hlt₁
              assumption
          case inr Heq₁ =>
            cases Hlt₂
            case inl Hlt₂ =>
              left
              simp [Heq₁]
              assumption
            case inr Heq₂ =>
              right
              simp [Heq₁, Heq₂]
              apply lt_trans Heq₁.2 Heq₂.2
        case inr Heq₁ =>
          left
          rw [←Heq₁.1,←Heq₁.2]
          assumption
      case inr Heq₁ =>
        cases H₂
        case inl Hlt₁ =>
          left
          simp [Heq₁]
          assumption
        case inr Heq₂ =>
          right
          simp [Heq₁,Heq₂]

  lt_iff_le_not_le m₁ m₂ := by
    constructor
    case mp =>
      intros H
      cases m₁
      case mk p₁ c₁ =>
      cases m₂
      case mk p₂ c₂ =>
        unfold LE.le
        simp [instLEMessageSig]
        constructor
        case left =>
          left
          assumption
        case right =>
          unfold LT.lt at *
          simp [instLTMessageSig] at *
          cases H
          case inl H =>
            constructor
            case left =>
              constructor
              case left =>
                exact le_of_lt H
              case right =>
                intro Heq
                simp [Heq] at H
            case right =>
              intro Heq
              simp [Heq] at H
          case inr H =>
            obtain ⟨H₁,H₂⟩ := H
            constructor
            constructor
            · exact le_of_eq H₁
            · intro Heq
              exact le_of_lt H₂
            · intro H
              exact ne_of_gt H₂
    case mpr =>
      intro ⟨H₁,H₂⟩
      cases m₁
      case mk p₁ c₁ =>
      cases m₂
      case mk p₂ c₂ =>
        unfold LT.lt
        unfold LE.le at *
        simp [instLTMessageSig, instLEMessageSig] at *
        cases H₁
        case inl H₁ =>
          cases H₁
          case inl H₁ =>
            left
            assumption
          case inr H₁ =>
            right
            assumption
        case inr H₁ =>
          simp [H₁] at H₂

instance: PartialOrder MessageSig where
  le_antisymm m₁ m₂ := by
    intros H₁ H₂
    cases m₁
    case mk p₁ c₁ =>
    cases m₂
    case mk p₂ c₂ =>
      unfold LE.le at H₁
      unfold LE.le at H₂
      simp [Preorder.toLE, instPreorderMessageSig, instLEMessageSig] at *
      cases H₁
      case inl H₁ =>
        cases H₂
        case inl H₂ =>
          unfold LT.lt at H₁
          unfold LT.lt at H₂
          simp [instLTMessageSig] at *
          cases H₁
          case inl H₁ =>
            cases H₂
            case inl H₂ =>
              have Hcontra: ¬ (p₂ < p₁) := by exact not_lt_of_gt H₁
              contradiction
            case inr H₂ =>
              simp [H₂] at H₁
          case inr H₁ =>
            cases H₂
            case inl H₂ =>
              simp [H₁] at H₂
            case inr H₂ =>
              have H₁' := H₁.2
              have H₂' := H₂.2
              have Hcontra : ¬ (c₂ < c₁) := by exact not_lt_of_gt H₁'
              contradiction
        case inr H₂ =>
          simp [H₁, H₂]
      case inr H₁ =>
        simp [H₁]

theorem MessageSig.le_total (m₁ m₂ : MessageSig):
  m₁ ≤ m₂  ∨ m₂ ≤ m₁ :=
by
  simp [LE.le]
  cases m₁ ; case mk p₁ c₁ =>
  cases m₂ ; case mk p₂ c₂ =>
    have Hptot := LinearOrder.le_total p₁ p₂
    have Hctot := LinearOrder.le_total c₁ c₂
    cases Hptot
    case inl Hple =>
      have Hple' : p₁ < p₂ ∨ p₁ = p₂ := by
        exact Decidable.lt_or_eq_of_le Hple
      cases Hple'
      case inl Hplt =>
        cases Hctot
        case inl Hcle =>
          have Hcle' : c₁ < c₂ ∨ c₁ = c₂ := by
            exact Decidable.lt_or_eq_of_le Hcle
          cases Hcle'
          case inl Hclt =>
            left ; left
            exact MessageSig_lt_prio (p₁, c₁) (p₂, c₂) Hplt
          case inr Hceq =>
            simp [Hceq]
            left
            left
            exact MessageSig_lt_prio (p₁, c₂) (p₂, c₂) Hplt
        case inr Hcle =>
          left
          left
          exact MessageSig_lt_prio (p₁, c₁) (p₂, c₂) Hplt
      case inr Hpeq =>
        simp [Hpeq]
        unfold LT.lt
        simp [instLTMessageSig]
        cases Hctot
        case inl Hcle =>
          left
          exact Decidable.lt_or_eq_of_le Hcle
        case inr Hcle =>
          right
          exact Decidable.lt_or_eq_of_le Hcle
    case inr Hple =>
      have Hple' : p₂ < p₁ ∨ p₂ = p₁ := by
        exact Decidable.lt_or_eq_of_le Hple
      cases Hple'
      case inl Hplt =>
        cases Hctot
        case inl Hcle =>
          have Hcle' : c₁ < c₂ ∨ c₁ = c₂ := by
            exact Decidable.lt_or_eq_of_le Hcle
          cases Hcle'
          case inl Hclt =>
            right ; left
            exact MessageSig_lt_prio (p₂, c₂) (p₁, c₁) Hplt
          case inr Hceq =>
            simp [Hceq]
            right
            left
            exact MessageSig_lt_prio (p₂, c₂) (p₁, c₂) Hplt
        case inr Hcle =>
          right
          left
          exact MessageSig_lt_prio (p₂, c₂) (p₁, c₁) Hplt
      case inr Hpeq =>
        simp [Hpeq]
        unfold LT.lt
        simp [instLTMessageSig]
        cases Hctot
        case inl Hcle =>
          left
          exact Decidable.lt_or_eq_of_le Hcle
        case inr Hcle =>
          right
          exact Decidable.lt_or_eq_of_le Hcle

instance: Min MessageSig where
  min := fun m₁ m₂ =>
    if m₁ ≤ m₂ then m₁ else m₂

instance: Max MessageSig where
  max := fun m₁ m₂ =>
    if m₁ < m₂ then m₂ else m₁

instance: LinearOrder MessageSig where
  le_total m₁ m₂ := by
    exact MessageSig.le_total m₁ m₂

  decidableLE m₁ m₂ := by
    simp
    unfold LE.le
    simp [Preorder.toLE, PartialOrder.toPreorder, instPartialOrderMessageSig,
          instPreorderMessageSig, instLEMessageSig]
    exact instDecidableOr

  min_def m₁ m₂ := by
    unfold Min.min
    simp [instMinMessageSig]

  max_def m₁ m₂ := by
    unfold Max.max
    simp [instMaxMessageSig]
    unfold LE.le
    simp [Preorder.toLE, PartialOrder.toPreorder, instPartialOrderMessageSig,
          instPreorderMessageSig, instLEMessageSig]
    split
    case isTrue H₁ =>
      simp [H₁]
    case isFalse H₁ =>
      simp [H₁]
      split
      case isTrue H₂ =>
        assumption
      case isFalse H₂ =>
        rfl

theorem MessageSig.le_prio (m₁ m₂ : MessageSig):
  m₁ ≤ m₂ → m₁.1 ≤ m₂.1 :=
by
  intro Hle
  unfold LE.le at Hle
  simp [instLEMessageSig] at Hle
  cases Hle
  case inl Hlt =>
    unfold LT.lt at Hlt
    simp [instLTMessageSig] at Hlt
    cases Hlt
    case inl H => exact le_of_lt H
    case inr H => simp [H]
  case inr Heq =>
    exact le_of_eq (congrArg Prod.fst Heq)

instance [DecidableEq α]: LT (Message α) where
  lt m₁ m₂ := m₁.sig < m₂.sig

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
    apply instDecidableRelMessageSigLt

instance Message.instDecidableLE [DecidableEq α] : DecidableRel (α := Message α) (·≤·) :=
  fun m₁ m₂ ↦  by
    simp
    unfold LE.le
    simp [instLEMessage]
    exact instDecidableOr

theorem Message.sigLT [DecidableEq α] (m₁ m₂ : Message α):
  m₁ < m₂ → m₁.sig < m₂.sig :=
by
  intro H
  exact H

theorem Message.sigLE [DecidableEq α] (m₁ m₂ : Message α):
  m₁ ≤ m₂ → m₁.sig ≤ m₂.sig :=
by
  intro Hle
  unfold LE.le at *
  simp [instLEMessage] at Hle
  simp [instLEMessageSig]
  cases Hle
  case inl Hlt =>
    left
    exact Hlt
  case inr Heq =>
    right
    exact congrArg sig Heq

theorem Message.sigLTconv [DecidableEq α] (m₁ m₂ : Message α):
  m₁.sig < m₂.sig → m₁ < m₂ :=
by
  intro H
  exact H

structure MQ3 (α : Type 0) [instDec: DecidableEq α] (ctx : MQContext)
    extends MQ2 α ctx where

@[simp]
def MQ3.lift [DecidableEq α] (mq : MQ3 α ctx) : MQ2 α ctx :=
  mq.toMQ2

@[simp]
def MQ3.sigs [DecidableEq α] (mq : MQ3 α ctx) : List MessageSig :=
  List.map Message.sig mq.queue

theorem MQ3.not_sig_not_elem [DecidableEq α] (mq : MQ3 α ctx) (msg : Message α):
  msg.sig ∉ mq.sigs → msg ∉ mq.queue :=
by
  simp
  intros Hsig Hmsg
  have Hsig' := Hsig msg Hmsg
  contradiction

instance [instDec: DecidableEq α]: Machine MQContext (MQ3 α (instDec:=instDec) ctx) where
  context := ctx
  invariant mq := mq.queue.length ≤ ctx.maxCount
                  ∧ (∀ msg ∈ mq.queue, msg.timestamp < mq.clock)
                  ∧ (∀ msg₁ ∈ mq.queue, ∀ msg₂ ∈ mq.queue, msg₁.timestamp = msg₂.timestamp → msg₁ = msg₂)
                  ∧ (∀ msg ∈ mq.queue, ctx.minPrio ≤ msg.prio ∧ msg.prio ≤ ctx.maxPrio)
                  ∧ mq.queue.Nodup
                  ∧ mq.sigs.Sorted (·≥·)
  reset := { queue := [], clock := 0}

theorem MQ3.clock_free [DecidableEq α] (mq : MQ3 α ctx):
  Machine.invariant mq → ∀ x, ∀ p, ⟨⟨x, mq.clock⟩, p⟩ ∉ mq.messages :=
by
  simp [Machine.invariant]
  intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv₆ x p Hin
  have Hinv₂' := Hinv₂ ⟨⟨x, mq.clock⟩, p⟩ Hin
  simp at Hinv₂' -- contradiction


theorem List_perm_Nodup (xs ys : List α):
  xs.Perm ys
  → xs.Nodup
  → ys.Nodup :=
by
  intros H₁ H₂
  exact List.Perm.nodup H₁ H₂

/-
theorem List_perm_length (xs ys : List α):
  xs.Perm ys
  → xs.length = ys.length :=
by
  intro H
  exact List.Perm.length_eq H
-/

/- Remark : Strong refinement is not possible because equality of
abstract state is too strong a requirement
(one cannot recover the initial - arbibrary - ordering of the
abstract event queue).

Functional refinement is also not possible because one cannot
"reinvent" the order at the abstract level when lifting the concrete state
-/
instance [instDec: DecidableEq α] : Refinement (MQ2 α ctx) (MQ3 α ctx) where

  refine (amq : MQ2 α ctx) (mq : MQ3 α ctx) :=
    mq.queue.Perm amq.queue
    ∧ mq.clock = amq.clock

  refine_safe (amq : MQ2 α ctx) (mq : MQ3 α ctx) := by
    simp [Machine.invariant]
    intro Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv₆ Href₁ Href₂
    constructor
    · have Hlen : mq.queue.length = amq.queue.length := by
        exact List.Perm.length_eq Href₁
      exact le_of_eq_of_le (id (Eq.symm Hlen)) Hinv₁
    constructor
    · intros msg Hmsg
      simp [←Href₂]
      have Hin : msg ∈ mq.queue := by
        exact (List.Perm.mem_iff (id (List.Perm.symm Href₁))).mp Hmsg
      exact Hinv₂ msg Hin
    constructor
    · intros msg₁ Hmsg₁ msg₂ Hmsg₂ Hts
      have Hin₁ : msg₁ ∈ mq.queue := by
        exact (List.Perm.mem_iff (id (List.Perm.symm Href₁))).mp Hmsg₁
      have Hin₂ : msg₂ ∈ mq.queue := by
        exact (List.Perm.mem_iff (id (List.Perm.symm Href₁))).mp Hmsg₂
      exact Hinv₃ msg₁ Hin₁ msg₂ Hin₂ Hts
    constructor
    · intros msg Hmsg
      have Hin : msg ∈ mq.queue := by
        exact (List.Perm.mem_iff (id (List.Perm.symm Href₁))).mp Hmsg
      exact Hinv₄ msg Hin
    · exact List_perm_Nodup mq.queue amq.queue Href₁ Hinv₅

  /- Cannot lift : don't know how to restore the MQ2 ordering of messages
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
  -/

def MQ3.Init [instDec: DecidableEq α] : InitREvent (MQ2 α ctx) (MQ3 α ctx) Unit Unit :=
  newInitREvent'' MQ2.Init.toInitEvent {
    init _ := { queue := [], clock := 0}
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
  { queue := mq.queue.orderedInsert (·≥·) ⟨⟨params.1, mq.clock⟩, params.2⟩,
                  clock := mq.clock + 1 }

theorem insertionSorted_Sorted (R : α → α → Prop) [DecidableRel R] [IsTotal α R] [IsTrans α R] (xs : List α):
  xs.Sorted R → (xs.orderedInsert R x).Sorted R :=
by
  intro Hsort
  refine List.Sorted.orderedInsert x xs Hsort

theorem insertion_Map [DecidableEq α] (mqueue : List (Message α)) (x : Message α):
  x.sig ∉ List.map Message.sig mqueue
  → List.map Message.sig (mqueue.orderedInsert (·≥·) x) = (List.map Message.sig mqueue).orderedInsert (·≥·) x.sig :=
by
  intro Hnotin
  refine
    List.map_orderedInsert (fun x1 x2 => x1 ≥ x2) (fun x1 x2 => x1 ≥ x2) Message.sig mqueue x ?_ ?_
  case _ =>
    intro ms Hms
    constructor
    case mp =>
      simp
      intro H
      exact Message.sigLE x ms H
    case mpr =>
      simp
      have Hin : ms.sig ∈ List.map Message.sig mqueue := by
        exact List.mem_map_of_mem Message.sig Hms
      have Hneq : ms.sig ≠ x.sig := by
        exact ne_of_mem_of_not_mem Hin Hnotin
      unfold LE.le
      simp [instLEMessageSig, instLEMessage]
      intro Hsig
      cases Hsig
      case inl Hlt =>
        left
        exact Hlt
      case inr Heqs =>
        rw [Heqs] at Hneq
        contradiction
  case _ =>
    intro ms Hms
    simp
    constructor
    case mp =>
      intro H
      exact Message.sigLE ms x H
    case mpr =>
      have Hin : ms.sig ∈ List.map Message.sig mqueue := by
        exact List.mem_map_of_mem Message.sig Hms
      have Hneq : ms.sig ≠ x.sig := by
        exact ne_of_mem_of_not_mem Hin Hnotin
      unfold LE.le
      simp [instLEMessageSig, instLEMessage]
      intro Hsig
      cases Hsig
      case inl Hlt =>
        left
        exact Hlt
      case inr Heqs =>
        rw [Heqs] at Hneq
        contradiction

theorem MessageSig_orderedInsert_Sorted (sigs : List MessageSig):
  sigs.Sorted (·≥·)
  → (sigs.orderedInsert (·≥·) x).Sorted (·≥·) :=
by
  intro H
  exact insertionSorted_Sorted (fun x1 x2 => x1 ≥ x2) sigs H

theorem Sorted_NotIn (R : α → α → Prop) [DecidableRel R] (x y : α) (xs : List α):
  y ≠ x → y ∉ xs → y ∉ List.orderedInsert R x xs :=
by
  intros Hneq Hnotin
  rw [@List.mem_orderedInsert]
  intro Hcontra
  cases Hcontra <;> contradiction

theorem Sorted_Nodup [DecidableEq α] (R : α → α → Prop) [DecidableRel R] (x : α) (xs : List α):
  xs.Nodup → x ∉ xs → (List.orderedInsert R x xs).Nodup :=
by
  induction xs
  case nil => simp
  case cons y xs Hind =>
    simp
    intros Hy Hnd Hneq Hni
    split
    case isTrue HR =>
      simp [Hneq, Hni, Hy, Hnd]
    case isFalse HR =>
      simp
      simp [*]
      intro Heq
      simp [Heq] at Hneq

def MQ3.Enqueue [DecidableEq α]: OrdinaryREvent (MQ2 α ctx) (MQ3 α ctx) (α × Prio) Unit :=
  newREvent' MQ2.Enqueue.toOrdinaryEvent {
    guard := MQ3.enqueue_guard

    action mq ps _ := MQ3.enqueue_action mq ps

    safety := fun mq (x, px) => by
      intro Hinv Hgrd
      have Hclk := MQ3.clock_free mq Hinv
      revert Hgrd Hinv
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
      · have Hni : { payload := x, timestamp := mq.clock, prio := px } ∉ mq.messages := by
            exact Hclk x px
        have Hnotin : { payload := x, timestamp := mq.clock, prio := px } ∉ mq.queue := by
          rw [← @List.mem_toFinset]
          exact Hclk x px
        apply Sorted_Nodup <;> assumption
      · rw [insertion_Map]
        · exact MessageSig_orderedInsert_Sorted (List.map Message.sig mq.queue) Hinv₆
        · have Hdiff : ∀ msg : Message α, msg.timestamp = mq.clock → msg.sig ∉ mq.sigs := by
            intros msg Hmsg
            simp
            intro msg' Hmsg'
            have Hinv₂' := Hinv₂ msg' Hmsg'
            simp [Message.sig]
            intro Hp
            rw [Hmsg]
            intro Hcontra
            simp [Hcontra] at Hinv₂'
          apply Hdiff
          simp

    lift_in := fun (x, px) => (x, px)

    strengthening := fun mq (x, px) => by
      simp [Machine.invariant, MQ2.Enqueue, Refinement.refine, enqueue_guard]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv₆ Hgrd₁ Hgrd₂ Hgrd₃ amq Href₁ Href₂
      constructor
      · have Hlen : mq.queue.length = amq.queue.length := by
          exact List.Perm.length_eq Href₁
        rw [←Hlen]
        exact Hgrd₁
      · exact ⟨Hgrd₂, Hgrd₃⟩

    simulation := fun mq (x, px) => by
      simp [Machine.invariant, MQ2.Enqueue, MQ3.enqueue_guard, MQ3.enqueue_action, Refinement.refine]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv₆ Hgrd₁ Hgrd₂ Hgrd₃ amq Href₁ Href₂
      constructor
      · rw [←Href₂]
        apply List.Perm.trans (l₂:=({ payload := x, timestamp := mq.clock, prio := px } :: mq.queue))
        · apply List.perm_orderedInsert
        · exact List.Perm.cons { payload := x, timestamp := mq.clock, prio := px } Href₁

      · simp [Href₂]
  }

def MQ3.priorities [DecidableEq α] (mq : MQ3 α ctx) : Finset Prio :=
  mq.queue.foldl (fun ps msg => ps ∪ {msg.prio}) ∅

theorem MQ3.lift_Prios [DecidableEq α] (mq : MQ3 α ctx):
  mq.lift.priorities = mq.priorities :=
by
  simp [MQ2.priorities, MQ3.priorities]

theorem MQ3_prios_in [DecidableEq α] (mq : MQ3 α ctx):
  ∀ msg ∈ mq.messages, msg.prio ∈ mq.priorities :=
by
  have H := MQ2_prios_in mq.lift
  rw [MQ3.lift_Prios] at H
  exact H

theorem MQ3.queue_in [DecidableEq α] (mq : MQ3 α ctx) (msg : Message α):
  msg ∈ mq.queue ↔ msg ∈ mq.lift.queue :=
by
  exact Eq.to_iff rfl

def MQ3.maxPrio [DecidableEq α] (mq : MQ3 α ctx) : Prio :=
  mq.lift.maxPrio

theorem MQ3.maxPrio_max [DecidableEq α] (mq : MQ3 α ctx) :
  ∀ msg ∈ mq.queue, msg.prio ≤ mq.maxPrio :=
by
  have H : ∀ msg ∈ mq.lift.queue, msg.prio ≤ mq.lift.maxPrio := by
    intros msg Hmsg
    exact MQ2.maxPrio_max mq.lift msg Hmsg
  intros msg Hmsg
  exact H msg Hmsg

theorem MQ3.maxPrio_in [DecidableEq α] (mq : MQ3 α ctx):
  Finset.Nonempty mq.priorities
  → mq.maxPrio ∈ mq.priorities :=
by
  rw [← @lift_Prios]
  apply MQ2.maxPrio_in

theorem MQ3.msgEx [DecidableEq α] (mq : MQ3 α ctx):
  ∀ prio ∈ mq.priorities, ∃ msg ∈ mq.messages, msg.prio = prio :=
by
  rw [← @lift_Prios, ← @lift_Messages]
  apply MQ2.msgEx mq.lift

def MQ3.maxElemEx [DecidableEq α] (mq : MQ3 α ctx):
  mq.queue ≠ []
  → ∃ msg ∈ mq.queue, msg.prio = mq.maxPrio :=
by
  intro Hne
  have Hlift := MQ2.maxElemEx mq.lift
  simp [lift_Messages] at Hlift
  have Hlift' := Hlift Hne
  obtain ⟨msg, Hmsg, Hprio⟩ := Hlift'
  exists msg

def errMessage {α : Type} [DecidableEq α] [Inhabited α] : Message α :=
  {timestamp := Clock.mk 0, prio := Prio.mk 0, payload := default}

theorem List_Nodeup_tail (xs : List α):
  xs.Nodup → xs.tail.Nodup :=
by
  intro Hxs
  cases xs
  case nil => simp
  case cons x xs =>
    simp at Hxs
    simp [Hxs]

theorem List_Perm_in (xs ys : List α):
  xs.Perm ys
  → ∀ x ∈ xs, x ∈ ys :=
by
  intros H x Hxs
  exact (List.Perm.mem_iff H).mp Hxs

theorem List_mem_not_head:
  x ≠ y → x ∈ y :: xs → x ∈ xs :=
by
  intros H₁ H₂
  exact List.mem_of_ne_of_mem H₁ H₂


def MQ3.Dequeue [DecidableEq α] [Inhabited α]: OrdinaryRDetEvent (MQ2 α ctx) (MQ3 α ctx) Unit (α × Prio) :=
  newRDetEvent MQ2.Dequeue.toOrdinaryNDEvent {
    lift_in := id
    lift_out := id
    guard (mq : MQ3 α ctx) _ := mq.queue ≠ []

    action (mq : MQ3 α ctx) x  grd :=
      let msg := mq.queue.head grd
      ((msg.payload, msg.prio), {mq with queue := mq.queue.tail})

    safety mq _ := by
      simp [Machine.invariant]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv₆ Hgrd
      constructor
      · exact Nat.le_add_right_of_le Hinv₁
      constructor
      · intros msg Hmsg
        have Hmsg': msg ∈ mq.queue := by
          exact List.mem_of_mem_tail Hmsg
        exact Hinv₂ msg Hmsg'
      constructor
      · intros msg₁ Hmsg₁ msg₂ Hmsg₂
        apply Hinv₃
        · exact List.mem_of_mem_tail Hmsg₁
        · exact List.mem_of_mem_tail Hmsg₂
      constructor
      · intros msg Hmsg
        apply Hinv₄ ; exact List.mem_of_mem_tail Hmsg
      constructor
      · exact List_Nodeup_tail mq.queue Hinv₅
      · exact List.Sorted.tail Hinv₆

    strengthening mq _ := by
      simp [Machine.invariant, Refinement.refine, MQ2.Dequeue]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv₆ Hgrd amq Href₁ Href₂
      intro Hamq
      simp [Hamq] at Href₁
      contradiction

    simulation mq _ := by
      simp [Machine.invariant, Refinement.refine, MQ2.Dequeue]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv₆ Hgrd amq Href₁ Href₂
      exists {clock := amq.clock, queue := amq.queue.erase (mq.queue.head Hgrd)}
      have Hmq: mq.queue = (mq.queue.head Hgrd) :: mq.queue.tail := by
          exact Eq.symm (List.head_cons_tail mq.queue Hgrd)
      constructor
      · have Hhead: mq.queue.head Hgrd ∈ mq.queue := by
          exact List.head_mem Hgrd
        have Hhead': mq.queue.head Hgrd ∈ amq.queue := by
          exact List_Perm_in mq.queue amq.queue Href₁ (mq.queue.head Hgrd) Hhead
        exists mq.queue.head Hgrd
        simp [Hhead']
        intros msg Hmsg Hmsg'
        have H₁: (mq.queue.head Hgrd).prio = (mq.queue.head Hgrd).sig.1 := by
          rfl
        rw [H₁]
        have Hsig: msg.sig ∈ List.map Message.sig mq.queue := by
          refine List.mem_map_of_mem Message.sig ?_
          exact List_Perm_in amq.queue mq.queue (id (List.Perm.symm Href₁)) msg Hmsg
        have Hmsg'' : msg ∈ mq.queue := by
          exact List_Perm_in amq.queue mq.queue (id (List.Perm.symm Href₁)) msg Hmsg
        have Hsort :  List.Sorted (·≥·) (List.map Message.sig ((mq.queue.head Hgrd) :: mq.queue.tail)) := by
          rw [← Hmq]
          exact Hinv₆
        have Hmsg''': msg ∈ mq.queue.tail := by
          apply List.mem_of_ne_of_mem (y:=mq.queue.head Hgrd)
          · exact Hmsg'
          · rw [←Hmq]
            exact Hmsg''
        have Hsup: msg.sig ≤ (mq.queue.head Hgrd).sig := by
          apply List.rel_of_sorted_cons Hsort
          exact List.mem_map_of_mem Message.sig Hmsg'''
        have Hp: msg.prio = msg.sig.1 := rfl
        rw [Hp]
        exact MessageSig.le_prio msg.sig (mq.queue.head Hgrd).sig Hsup
      constructor
      · simp
        have Hmq': mq.queue.tail = mq.queue.erase (mq.queue.head Hgrd) := by
          have Hmq'' : ((mq.queue.head Hgrd) :: mq.queue.tail).erase (mq.queue.head Hgrd)
                       = mq.queue.tail := by
            exact List.erase_cons_head (mq.queue.head Hgrd) mq.queue.tail
          rw [←Hmq'']
          rw [←Hmq]
        rw [Hmq']
        exact List.Perm.erase (mq.queue.head Hgrd) Href₁
      · simp [Href₂]
  }

end MQueue
