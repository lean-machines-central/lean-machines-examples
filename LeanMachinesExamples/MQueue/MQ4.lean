
import LeanMachinesExamples.MQueue.MQ3

namespace MQueue

open Clocked
open Prioritized

structure MQ4 (α : Type 0) [instDec: DecidableEq α] (ctx : MQContext)
  extends Clocked where
  queue : Array (Message α)

def MQ4.lift [DecidableEq α] (mq : MQ4 α ctx) : MQ3 α ctx := {
  clock := mq.clock,
  queue := mq.queue.toList
}

def MQ4.unlift [DecidableEq α] (_ : MQ4 α ctx) (amq' : MQ3 α ctx) : MQ4 α ctx := {
  clock := amq'.clock,
  queue := amq'.queue.toArray
}

def MQ4.sigs [DecidableEq α] (mq : MQ4 α ctx) : List MessageSig :=
  MQ3.sigs mq.lift

instance [instDec: DecidableEq α]: Machine MQContext (MQ4 α (instDec:=instDec) ctx) where
  context := ctx
  invariant mq := mq.queue.size ≤ ctx.maxCount
                  ∧ (∀ msg ∈ mq.queue, msg.timestamp < mq.clock)
                  ∧ (∀ msg₁ ∈ mq.queue, ∀ msg₂ ∈ mq.queue, msg₁.timestamp = msg₂.timestamp → msg₁ = msg₂)
                  ∧ (∀ msg ∈ mq.queue, ctx.minPrio ≤ msg.prio ∧ msg.prio ≤ ctx.maxPrio)
                  ∧ mq.queue.toList.Nodup
                  ∧ mq.sigs.Sorted (·≥·)
  reset := { queue := #[], clock := 0}

instance [DecidableEq α]: SRefinement (MQ3 α ctx) (MQ4 α ctx) where
  lift := MQ4.lift
  lift_safe mq := by
    simp [Machine.invariant]
    intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv₆
    simp [MQ4.lift]
    constructor
    · exact Hinv₁
    constructor
    · intros msg Hmsg
      exact Hinv₂ msg Hmsg
    constructor
    · apply Hinv₃
    constructor
    · apply Hinv₄
    constructor
    · exact Hinv₅
    · exact Hinv₆

  unlift := MQ4.unlift
  lu_reset mq := by
    simp [FRefinement.lift, Machine.reset, MQ4.unlift]
    simp [MQ4.lift]
  lift_unlift mq amq := by
    simp [FRefinement.lift, MQ4.unlift, MQ4.lift]


def MQ4.Init [DecidableEq α] : InitREvent (MQ3 α ctx) (MQ4 α ctx) Unit Unit :=
  newInitSREvent'' MQ3.Init.toInitEvent {
    init := { queue := #[], clock := 0}
    safety _ := by
      simp [Machine.invariant]
      simp [MQ4.sigs, MQ4.lift]
    strengthening _ := by simp [Machine.invariant, MQ3.Init]
    simulation _ := by simp [FRefinement.lift, MQ3.Init, MQ4.lift]
  }

-- The following are not available ... but they should at some point ...
axiom Array_insertionSortSize {α : Type} (lt : α → α → Bool) (as : Array α):
  as.insertionSort (lt:=lt).size = as.size

axiom Array_insertionSortMem {α : Type} (lt : α → α → Bool) (as : Array α) (x : α):
  x ∈ as → x ∈ as.insertionSort (lt:=lt)

axiom Array_insertionSortMemConv {α : Type} (lt : α → α → Bool) (as : Array α) (x : α):
  x ∈ as.insertionSort (lt:=lt) → x ∈ as



def MQ4.Enqueue [DecidableEq α]: OrdinaryREvent (MQ3 α ctx) (MQ4 α ctx) (α × Prio) Unit :=
  newSREvent' MQ3.Enqueue.toOrdinaryEvent {
    lift_in := id

    guard := fun mq (x, p) =>
       mq.queue.size < ctx.maxCount
       ∧ ctx.minPrio ≤ p ∧ p ≤ ctx.maxPrio

    action := fun mq (x, p) => { clock := mq.clock + 1,
                                 queue := Array.insertionSort
                                   (mq.queue.push {payload:=x, prio:=p, timestamp:=mq.clock})
                                   (·≥·)}

    safety := fun mq (x, p) => by
      simp [Machine.invariant]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv₆ Hgrd₁ Hgrd₂ Hgrd₃
      constructor
      · have Hpush: (mq.queue.push { payload := x, timestamp := mq.clock, prio := p }).size
                    = mq.queue.size + 1 := by
          exact Array.size_push mq.queue { payload := x, timestamp := mq.clock, prio := p }
        rw [@Array_insertionSortSize]
        rw [Hpush]
        exact Hgrd₁
      constructor
      · intros msg Hmsg
        have Hmsg' : msg ∈ mq.queue.push { payload := x, timestamp := mq.clock, prio := p } := by
          apply Array_insertionSortMemConv
          · exact Hmsg
        have Hmsg'' : msg ∈ mq.queue ∨ msg = { payload := x, timestamp := mq.clock, prio := p } := by
          exact Array.mem_push.mp Hmsg'
        cases Hmsg''
        case _ Hmsg'' =>
          have Hts: msg.timestamp < mq.clock := by
            exact Hinv₂ msg Hmsg''
          apply lt_trans (b:=mq.clock)
          · assumption
          · exact Clocked.succ_lt mq.clock
        case _ Hmsg'' =>
          simp [Hmsg'']
          exact Clocked.succ_lt mq.clock
      constructor
      · intros msg₁ Hmsg₁ msg₂ Hmsg₂
        have Hmsg₁' : msg₁ ∈ mq.queue.push { payload := x, timestamp := mq.clock, prio := p } := by
          apply Array_insertionSortMemConv
          · exact Hmsg₁
        have Hmsg₁'' : msg₁ ∈ mq.queue ∨ msg₁ = { payload := x, timestamp := mq.clock, prio := p } := by
          exact Array.mem_push.mp Hmsg₁'
        have Hmsg₂' : msg₂ ∈ mq.queue.push { payload := x, timestamp := mq.clock, prio := p } := by
          apply Array_insertionSortMemConv
          · exact Hmsg₂
        have Hmsg₂'' : msg₂ ∈ mq.queue ∨ msg₂ = { payload := x, timestamp := mq.clock, prio := p } := by
          exact Array.mem_push.mp Hmsg₂'
        intro Hts
        cases Hmsg₁''
        case _ Hmsg₁'' =>
          cases Hmsg₂''
          case _ Hmsg₂'' =>
            exact Hinv₃ msg₁ Hmsg₁'' msg₂ Hmsg₂'' Hts
          case _ Hmsg₂'' =>
            have Hmsg₁''' : msg₁.timestamp < mq.clock := by
              exact Hinv₂ msg₁ Hmsg₁''
            simp [Hmsg₂''] at Hts
            rw [Hts] at Hmsg₁'''
            have Hcontra: ¬ (mq.clock < mq.clock) := by
              exact not_lt_of_gt Hmsg₁'''
            contradiction
        case _ Hmsg₁'' =>
          cases Hmsg₂''
          case _ Hmsg₂'' =>
            have Hmsg₂''' : msg₂.timestamp < mq.clock := by
              exact Hinv₂ msg₂ Hmsg₂''
            simp [Hmsg₁''] at Hts
            rw [←Hts] at Hmsg₂'''
            have Hcontra: ¬ (mq.clock < mq.clock) := by
              exact not_lt_of_gt Hmsg₂'''
            contradiction
          case _ Hmsg₂'' =>
            simp [Hmsg₁'', Hmsg₂'']
      constructor
      · intros msg Hmsg
        have Hmsg' : msg ∈ mq.queue.push { payload := x, timestamp := mq.clock, prio := p } := by
          apply Array_insertionSortMemConv
          · exact Hmsg
        have Hmsg'' : msg ∈ mq.queue ∨ msg = { payload := x, timestamp := mq.clock, prio := p } := by
          exact Array.mem_push.mp Hmsg'
        cases Hmsg''
        case _ Hmsg'' =>
          exact Hinv₄ msg Hmsg''
        case _ Hmsg'' =>
          simp [Hmsg'']
          exact ⟨Hgrd₂, Hgrd₃⟩
      constructor
      · sorry
      · sorry

    strengthening := fun mq (x, p) => by
      simp [MQ3.Enqueue, FRefinement.lift, MQ4.lift, MQ3.enqueue_guard]

    simulation := fun mq (x, p) => by
      simp [MQ3.Enqueue, FRefinement.lift, MQ3.enqueue_action]
      sorry
  }
