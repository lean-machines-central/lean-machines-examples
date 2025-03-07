
import LeanMachinesExamples.MQueue.MQ3

import LeanMachines.Refinement.Strong.Abstract

namespace MQueue

open Clocked
open Prioritized

structure MQ4 (α : Type 0) [instDec: DecidableEq α] (ctx : MQContext)
  extends MClocked where
  queue : Array (Message α)

def MQ4.lift [DecidableEq α] (mq : MQ4 α ctx) : MQ3 α ctx := {
  clock := mq.clock,
  queue := mq.queue.toList.reverse
}

def MQ4.unlift [DecidableEq α] (_ : MQ4 α ctx) (amq' : MQ3 α ctx) : MQ4 α ctx := {
  clock := amq'.clock,
  queue := amq'.queue.reverse.toArray
}

def MQ4.sigs [DecidableEq α] (mq : MQ4 α ctx) : List MessageSig :=
  MQ3.sigs mq.lift

instance [instDec: DecidableEq α]: Machine MQContext (MQ4 α (instDec:=instDec) ctx) where
  context := ctx
  invariant mq := mq.queue.size ≤ ctx.maxCount
                  ∧ (∀ msg ∈ mq.queue, msg.timestamp < mq.clock)
                  ∧ (∀ msg₁ ∈ mq.queue, ∀ msg₂ ∈ mq.queue, msg₁.timestamp = msg₂.timestamp ↔ msg₁ = msg₂)
                  ∧ (∀ msg ∈ mq.queue, ctx.minPrio ≤ msg.prio ∧ msg.prio ≤ ctx.maxPrio)
                  ∧ mq.queue.toList.Nodup
                  ∧ mq.sigs.Sorted (·≥·)
  default := { queue := #[], clock := 0}

theorem List_Sorted_append [Preorder α] (xs : List α) (x : α):
  (∀ y ∈ xs, y ≤ x) → List.Sorted (fun x₁ x₂ => x₁ ≤ x₂) xs
  → List.Sorted (fun x₁ x₂ => x₁ ≤ x₂) (xs ++ [x]) :=
by
  induction xs
  case nil => simp
  case cons x' xs Hind =>
    simp
    intros Hinf Hin Hinf' Hsort
    constructor
    case left =>
      intros z Hz
      cases Hz
      case inl Hz =>
        exact Hinf' z Hz
      case inr Hz =>
        exact le_of_le_of_eq Hinf (id (Eq.symm Hz))
    case right =>
      exact Hind Hin Hsort

theorem List_Sorted_append' [Preorder α] (xs : List α) (x : α):
  (∀ y ∈ xs, x ≤ y) → List.Sorted (fun x₁ x₂ => x₂ ≤ x₁) xs
  → List.Sorted (fun x₁ x₂ => x₂ ≤ x₁) (xs ++ [x]) :=
by
  induction xs
  case nil => simp
  case cons x' xs Hind =>
    simp
    intros Hinf Hin Hinf' Hsort
    constructor
    case left =>
      intros z Hz
      cases Hz
      case inl Hz =>
        exact Hinf' z Hz
      case inr Hz =>
        exact le_of_eq_of_le Hz Hinf
    case right =>
      exact Hind Hin Hsort

theorem List_Sorted_reverse [Preorder α] (xs : List α):
  List.Sorted (fun x1 x2 => x2 ≤ x1) xs
  → List.Sorted (fun x1 x2  => x1 ≤ x2) xs.reverse :=
by
  induction xs
  case nil => simp
  case cons x xs Hind =>
    simp
    intros Hinf Hsort
    apply List_Sorted_append (xs.reverse) x
    · intro y Hy
      have Hy' : y ∈ xs := by
        exact List.mem_reverse.mp Hy
      exact Hinf y Hy'
    · exact Hind Hsort

theorem List_Sorted_reverse' [Preorder α] (xs : List α):
  List.Sorted (fun x1 x2 => x1 ≤ x2) xs
  → List.Sorted (fun x1 x2  => x2 ≤ x1) xs.reverse :=
by
  induction xs
  case nil => simp
  case cons x xs Hind =>
    simp
    intro Hinf Hsort
    refine List_Sorted_append' xs.reverse x ?_ (Hind Hsort)
    intros y Hy
    have Hinf' := Hinf y
    apply Hinf'
    exact List.mem_reverse.mp Hy

instance [DecidableEq α] [Preorder α]: SRefinement (MQ3 α ctx) (MQ4 α ctx) where
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
    · simp [MQ4.sigs, MQ4.lift] at Hinv₆
      exact Hinv₆

  unlift := MQ4.unlift
  lu_default mq := by
    simp [FRefinement.lift, default, MQ4.unlift]
    simp [MQ4.lift]
  lift_unlift mq amq := by
    simp [FRefinement.lift, MQ4.unlift, MQ4.lift]

def MQ4.Init [DecidableEq α] [Preorder α]: InitREvent (MQ3 α ctx) (MQ4 α ctx) Unit Unit :=
  newInitSREvent'' MQ3.Init.toInitEvent {
    init _ := { queue := #[], clock := 0}
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

theorem Array_push_toList (as : Array α) (x : α):
  (as.push x).toList = as.toList ++ [x] :=
by
  apply Array.push_toList

theorem Array_push_Nodup (as : Array α) (x : α):
  as.toList.Nodup
  → x ∉ as
  → (as.push x).toList.Nodup :=
by
  intros Has Hx
  rw [@Array.push_toList]
  rw [@List.nodup_middle]
  simp
  simp [Has, Hx]

axiom Array_insertionSort_Perm {α} (as : Array α) (lt : α → α → Bool):
  as.toList.Perm
  (as.insertionSort (lt:=lt)).toList

theorem Array_insertionSort_Nodup (as : Array α) (lt : α → α → Bool):
  as.toList.Nodup
  → (as.insertionSort (lt:=lt)).toList.Nodup :=
by
  intro Hnd
  apply List.Nodup.perm (l:=as.toList) (l':=(as.insertionSort (lt:=lt)).toList)
  · exact Hnd
  · apply Array_insertionSort_Perm (as:=as)

axiom Array_insertionSort_Sorted {α} (as : Array α) (lt : α → α → Bool):
  (as.insertionSort (lt:=lt)).toList.Sorted (fun x₁ x₂ => lt x₁ x₂)

axiom Array_insertionSort_List_InsertionSort {α} (as : Array α) (lt : α → α → Bool):
  (as.insertionSort (lt:=lt)).toList = (as.toList).insertionSort (fun x₁ x₂ => lt x₁ x₂)

def MQ4.Enqueue [DecidableEq α] [Preorder α]: OrdinaryREvent (MQ3 α ctx) (MQ4 α ctx) (α × Prio) Unit :=
  newSREvent' MQ3.Enqueue.toOrdinaryEvent {
    lift_in := id

    guard := fun mq (x, p) =>
       mq.queue.size < ctx.maxCount
       ∧ ctx.minPrio ≤ p ∧ p ≤ ctx.maxPrio

    action := fun mq (x, p) _ => { clock := mq.clock + 1,
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
          · exact Clock.succ_lt mq.clock
        case _ Hmsg'' =>
          simp [Hmsg'']
          exact Clock.succ_lt mq.clock
      constructor
      · intros msg₁ Hmsg₁ msg₂ Hmsg₂
        exact Iff.symm (Message.timestamp_ax msg₁ msg₂)
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
      · refine
          Array_insertionSort_Nodup
            (mq.queue.push { payload := x, timestamp := mq.clock, prio := p })
            (fun x1 x2 => decide (x2 ≤ x1)) ?_
        refine Array_push_Nodup mq.queue { payload := x, timestamp := mq.clock, prio := p } Hinv₅ ?_
        intro Hcontra
        have Hinv₂' := Hinv₂ { payload := x, timestamp := mq.clock, prio := p } Hcontra
        simp at Hinv₂'
      · sorry

    strengthening := fun mq (x, p) => by
      simp [MQ3.Enqueue, FRefinement.lift, MQ4.lift, MQ3.enqueue_guard]

    simulation := fun mq (x, p) => by
      simp [MQ3.Enqueue, FRefinement.lift, MQ3.enqueue_action, MQ4.lift]
      intros Hinv Hgrd₁ Hgrd₂ Hgrd₃
      sorry
  }


def MQ4.Dequeue [DecidableEq α] [Inhabited α] [Preorder α]: OrdinaryREvent (MQ3 α ctx) (MQ4 α ctx) Unit (α × Prio) :=
  newSREvent MQ3.Dequeue.toOrdinaryEvent {
    lift_in := id
    lift_out := id
    guard mq _ := mq.queue.size > 0
    action mq _ grd := let msg := mq.queue[mq.queue.size-1]
                       ((msg.payload, msg.prio), { mq with queue := mq.queue.pop })

    safety mq _ grd := sorry
    simulation mq _ grd := sorry
    strengthening mq _ grd := sorry
  }

def MQ4.Discard [DecidableEq α] [Preorder α]: OrdinaryREvent (MQ3 α ctx) (MQ4 α ctx) Clock (List (Message α)) :=
  newAbstractSREvent MQ3.Discard.toOrdinaryEvent {
    step_inv mq clk := by sorry

  }

end MQueue
