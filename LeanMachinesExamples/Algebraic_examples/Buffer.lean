
import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent
import LeanMachines.NonDet.Ordinary
import LeanMachines.Event.Algebra.Ordinary

import LeanMachinesExamples.MQueue.MQ3
import LeanMachinesExamples.MQueue.Clocked

-- # Functors and Profunctors

-- if we want to specify new events that only differs from the ones already described by the
-- type of the input and the output, we want to combine our events with functions that allow us to transform
-- intro the input type and from the output type.

namespace MQueue


def MQN := MQueue.MQ3 Nat

def ContextExample : MQContext :=
  {
    maxCount := 5
    prop_maxCount := Nat.zero_lt_succ 4
    minPrio := 0
    maxPrio := 5
    minMaxOrd := Nat.zero_lt_succ 4
  }


def MachineExample : MQN ContextExample :=
  (MQueue.MQ3.Init.init (M := MQueue.MQ3 Nat ContextExample) () (by simp[MQ3.Init])).2

instance [DecidableEq α] [Repr α] : Repr (Message α) where
  reprPrec m _ :=
  match m with
  | Message.mk x y=>
    match x with
    | Message0.mk a b =>
    "( Prio : "++ (repr y.prio) ++ ", Message : "++ (repr a) ++ ", Clk : " ++ (repr b.val)++ " )"

instance [DecidableEq α] [Repr α]: Repr (MQ3 α ctx) where
  reprPrec m _ :=
  match m with
  | MQ3.mk (MQ2.mk mc l) => "mck : " ++ (repr mc.clock.val) ++ " " ++ (repr l)


#eval! (MQueue.MQ3.Enqueue.action MachineExample ⟨2,1⟩
  (by
    simp[MQ3.Enqueue,enqueue_guard,MachineExample,MQ3.Init,ContextExample]
    apply And.intro
    · exact Nat.lt_of_sub_eq_succ rfl
    · simp
      apply And.intro (right_eq_inf.mp rfl) (right_eq_inf.mp rfl)
  )).2

def Machine2 := (MQueue.MQ3.Enqueue.action MachineExample ⟨2,1⟩
  (by
    simp[MQ3.Enqueue,enqueue_guard,MachineExample,MQ3.Init,ContextExample]
    apply And.intro
    · exact Nat.lt_of_sub_eq_succ rfl
    · simp
      apply And.intro (right_eq_inf.mp rfl) (right_eq_inf.mp rfl)
  )).2

def DequeueEven : OrdinaryEvent (MQ3 Nat ctx) Unit Bool :=
  (λ x => x.1 %2 == 0) <$> MQ3.Dequeue.toOrdinaryEvent

def Machine3 : MQN ContextExample := {Machine2 with queue := []}

#check MQ3.mk
#check Clocked.MClocked.mk
#check Clocked.Clock.mk
-- example : ∃ m', DequeueEven.effect Machine2 ()
--   (by
--     simp[DequeueEven,MQ3.Dequeue,Machine2,MQ3.Enqueue,Functor.map]
--   )
--   (true,m'):=
--   by
--     simp[DequeueEven,MQ3.Dequeue,Machine2,MQ3.Enqueue,Functor.map]
--     -- m' corresponds to the machine that is obtained after removing the message
--     -- of Machine2
--     let m' : MQN ContextExample := {Machine2 with queue := []}
--     exists m'
--     exists 2
--     constructor
--     · exists 1
--     · omega
#eval DequeueEven.action Machine2 ()
  (by
    simp[DequeueEven,MQ3.Dequeue,Machine2,MQ3.Enqueue,MQ3.enqueue_action,Functor.map,mapEvent,map_Event,MachineExample,MQ3.Init]
  )


def Machine4 := (MQueue.MQ3.Enqueue.action Machine3 ⟨3,1⟩
  (by
    simp[MQ3.Enqueue,enqueue_guard,MachineExample,MQ3.Init,ContextExample]
    apply And.intro
    · exact Nat.lt_of_sub_eq_succ rfl
    · simp
      apply And.intro (right_eq_inf.mp rfl) (right_eq_inf.mp rfl)
  )).2


#eval DequeueEven.action Machine4 ()
  (by
    simp[DequeueEven,MQ3.Dequeue,Machine4,Machine3,MQ3.Enqueue,MQ3.enqueue_action,Functor.map,mapEvent,map_Event,MachineExample,MQ3.Init]
  )


def EnqueueChoice [DecidableEq α] (choose : List α → α): OrdinaryEvent (MQ3 α ctx) (List α × Prioritized.Prio) Unit :=
  Profunctor.dimap (λ (l,p) => (choose l,p)) id MQ3.Enqueue.toOrdinaryEvent


def choose_nat : List Nat → Nat :=
  List.foldl (λ x acc => if x > acc then x else acc) 0

#check EnqueueChoice (ctx := ContextExample) choose_nat
#eval Prod.snd $ (EnqueueChoice (ctx := ContextExample) choose_nat ).action Machine4 ([1,5,3,2],4)
  (by
    simp[EnqueueChoice,Profunctor.dimap,MQ3.Enqueue,Machine4,Machine3,ContextExample,MQ3.enqueue_action,MQ3.enqueue_guard]
    apply And.intro (Nat.zero_le 4) (Nat.le_succ 4)
  )


open Clocked

def EnqueueChoice' [DecidableEq α] (choose : List α → α): OrdinaryEvent (MQ3 α ctx) (List α × Prioritized.Prio) Unit :=
  let map_p {α' β' γ} (f : α' → β' ) (p : α'× γ):= (f p.1, p.2)
  newEvent'
  {

    guard m x := MQ3.Enqueue.guard m (map_p choose x)
    action m x grd :=(MQ3.Enqueue.action m (map_p choose x) grd).2
    safety mq x := MQ3.Enqueue.po.safety mq (map_p choose x)

  }

open Prioritized


def MQ3.PushForce [DecidableEq α] [Inhabited α]: OrdinaryEvent (MQ3 α ctx) (α × Prio) (Option (α × Prio)) :=
  newEvent
  {
    guard m x := m.queue.length ≤ ctx.maxCount ∧ ctx.minPrio ≤ x.2 ∧ x.2 ≤ ctx.maxPrio
    action m x hgrd :=
    by
      by_cases m.queue.length = ctx.maxCount
      case pos Hpos =>
        --let (o,m') := MQ3.Dequeue.action m ()
        let omq := (MQ3.Dequeue.action m ()
          (
            by
              simp[Dequeue]
              refine List.ne_nil_of_length_pos ?_
              rw[Hpos]
              exact ctx.prop_maxCount
          )
          )

        let (_,m'') := MQ3.Enqueue.action omq.2 x
          (
            by
              simp[Enqueue,Dequeue]
              unfold enqueue_guard
              constructor
              ·
                unfold omq
                simp[Dequeue]
                rw[Hpos]
                refine Nat.sub_one_lt (Nat.pos_iff_ne_zero.mp (ctx.prop_maxCount))
              exact hgrd.2
          )
        exact (omq.1,m'')
      case neg Hneg =>
        let (_,m') := MQ3.Enqueue.action m x
          (
            by
              simp[Enqueue,enqueue_guard]
              apply And.intro (Nat.lt_of_le_of_ne hgrd.1 Hneg) hgrd.2
          )
        exact (Option.none, m')

    safety m x hinv hgrd :=
    by
      by_cases m.queue.length = ctx.maxCount
      case pos Hpos =>
        simp[Hpos]
        let omq := MQ3.Dequeue.action m ()
          (
            by
              simp[Dequeue]
              refine List.ne_nil_of_length_pos ?_
              rw[Hpos]
              exact ctx.prop_maxCount
          )
        have hdequeue := MQ3.Dequeue.po.safety m () hinv
          (by
              simp[Dequeue]
              refine List.ne_nil_of_length_pos ?_
              rw[Hpos]
              exact ctx.prop_maxCount
          )
        exact MQ3.Enqueue.po.safety
          (omq).2 x hdequeue
            (
              by
                simp[Enqueue,Dequeue]
                unfold enqueue_guard
                constructor
                ·
                  unfold omq
                  simp[Dequeue]
                  rw[Hpos]
                  refine Nat.sub_one_lt (Nat.pos_iff_ne_zero.mp (ctx.prop_maxCount))
                exact hgrd.2
            )
      case neg Hneg =>
        simp[Hneg]
        exact MQ3.Enqueue.po.safety m x hinv
          (
            by
              simp[Enqueue,enqueue_guard]
              apply And.intro (Nat.lt_of_le_of_ne hgrd.1 Hneg) hgrd.2
          )
  }


def MQ3.DequeueEnqueue [DecidableEq α] [Inhabited α] : OrdinaryEvent (MQ3 α ctx) (α × Prio) (α × Prio) :=
  Profunctor.dimap (λ x => ((),x)) (λ (x,_) => x) (Arrow.split MQ3.Dequeue.toOrdinaryEvent MQ3.Enqueue.toOrdinaryEvent)


def MQ3.PushForce' [DecidableEq α] [Inhabited α] : OrdinaryEvent (MQ3 α ctx) (α × Prio) (Option (α × Prio)) :=
  let DequeueEnqueue := Profunctor.dimap (λ x => ((),x)) (λ (y,_) => y) (Arrow.split MQ3.Dequeue.toOrdinaryEvent MQ3.Enqueue.toOrdinaryEvent)
  let pushforce_or_push := ArrowChoice.splitIn DequeueEnqueue MQ3.Enqueue.toOrdinaryEvent
  let decide_from_machine := (λ (mq : (MQ3 α ctx)) x => if mq.queue.length = ctx.maxCount then Sum.inl x else Sum.inr x )

  (λ x => match x with |.inl l => Option.some l | .inr _ => Option.none)
  <$> (OrdinaryEvent.arrM decide_from_machine (>>>) pushforce_or_push)


def ctx_ex : MQContext :=
  {
    maxCount := 2,
    prop_maxCount := by simp,
    minPrio := Prio.mk 1,
    maxPrio := Prio.mk 5,
    minMaxOrd := by simp
  }

def MExample : MQ3 Nat ctx_ex :=
  (MQ3.Init.to_InitEvent.init () (by simp[MQ3.Init])).2

def MExample' : MQ3 Nat ctx_ex :=
  (MQ3.Enqueue.action MExample (3,4)
  (
    by
      simp[ctx_ex,MExample,MQ3.Init,MQ3.Enqueue,MQ3.enqueue_guard]
      constructor
      repeat exact right_eq_inf.mp rfl
  )).2

def MExample'' : MQ3 Nat ctx_ex :=
  (MQ3.Enqueue.action MExample' (4,1)
  (
    by
      simp[ctx_ex,MExample,MExample',MQ3.Init,MQ3.Enqueue,MQ3.enqueue_guard,MQ3.enqueue_action]
      constructor
      repeat exact right_eq_inf.mp rfl
  )).2


#eval MExample.queue
#eval MExample'.queue
#eval MExample''.queue

#eval (MQ3.DequeueEnqueue.action MExample'' ((2,2))
  (
    by
      simp[ctx_ex,MExample,MExample',MExample'',MQ3.Init]
      simp[MQ3.DequeueEnqueue,Arrow.split]
      simp[MQ3.Enqueue,MQ3.enqueue_guard,MQ3.enqueue_action]
      simp[MQ3.Dequeue]
      constructor
      · by_cases  ({ payload := 3, timestamp := 0, prio := 4 } : Message Nat) ≤ ({ payload := 4, timestamp := 0 + 1, prio := 1 } : Message Nat)
        case pos Hpos =>
          simp[Hpos]
        case neg Hneg =>
          simp[Hneg]
      · by_cases  ({ payload := 3, timestamp := 0, prio := 4 } : Message Nat) ≤ ({ payload := 4, timestamp := 0 + 1, prio := 1 } : Message Nat)
        case pos Hpos =>
          simp[Hpos]
          apply And.intro (right_eq_inf.mp rfl) (right_eq_inf.mp rfl)
        case neg Hneg =>
          simp[Hneg]
          apply And.intro (right_eq_inf.mp rfl) (right_eq_inf.mp rfl)
  )).2.queue

#eval! (MQ3.PushForce'.action MExample'' (2,2)
  (
    by
      simp[MQ3.PushForce']
      simp[OrdinaryEvent.arrM,_Event.arrM,ArrowChoice.splitIn,alt_Event,MQ3.DequeueEnqueue,Arrow.split,MQ3.Enqueue,MQ3.Dequeue]
      simp[Profunctor.dimap,Functor.map,mapEvent,map_Event]
      simp[MExample'',MExample',MExample,MQ3.Enqueue,MQ3.Init,MQ3.enqueue_action]
      simp[MQ3.enqueue_guard]
      simp[ctx_ex]
      have Hneg : ¬ ({ payload := 3, timestamp := 0, prio := 4 } ≤ ({ payload := 4, timestamp := 0 + 1, prio := 1 } : Message ℕ)) :=
        by
          simp[instLEMessage]
          simp[instLTMessage]
          simp[Message.sig]
          exact max_eq_left_iff.mp rfl
      simp[Hneg]
      exact And.intro (right_eq_inf.mp rfl) (right_eq_inf.mp rfl)
  )
  ).2.queue

#eval! (MQ3.PushForce'.action MExample'' (2,2)
(
    by
      simp[MQ3.PushForce']
      simp[OrdinaryEvent.arrM,_Event.arrM,ArrowChoice.splitIn,alt_Event,MQ3.DequeueEnqueue,Arrow.split,MQ3.Enqueue,MQ3.Dequeue]
      simp[Profunctor.dimap,Functor.map,mapEvent,map_Event]
      simp[MExample'',MExample',MExample,MQ3.Enqueue,MQ3.Init,MQ3.enqueue_action]
      simp[MQ3.enqueue_guard]
      simp[ctx_ex]
      have Hneg : ¬ ({ payload := 3, timestamp := 0, prio := 4 } ≤ ({ payload := 4, timestamp := 0 + 1, prio := 1 } : Message ℕ)) :=
        by
          simp[instLEMessage]
          simp[instLTMessage]
          simp[Message.sig]
          exact max_eq_left_iff.mp rfl
      simp[Hneg]
      exact And.intro (right_eq_inf.mp rfl) (right_eq_inf.mp rfl)
  )).1

end MQueue
