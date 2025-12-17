

import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent
import LeanMachines.NonDet.Ordinary
import LeanMachines.Event.Algebra.Ordinary

import LeanMachinesExamples.MQueue.Bounded

open Bounded
def Twoincr : OrdinaryEvent (Bounded ctx) Unit Unit :=
  do
    Incr
    Incr

def exemple : Bounded ({maxCount := 2, prop_maxCount := Nat.zero_lt_two}) :=
  let i:= Init.to_InitEvent.init (M := Bounded ({maxCount := 2, prop_maxCount := Nat.zero_lt_two})) () (by trivial)
  i.2


#eval exemple.count

#eval (Twoincr.action exemple ()
  (by
    simp[Twoincr,exemple]
    simp [Bind.bind, Pure.pure]
    simp[Init]
    simp [bindEvent]
    simp[Incr]
    simp [Bind.bind, Pure.pure]
    simp[bind_Event]
  )).2



def Add_n : OrdinaryEvent (Bounded ctx) Nat Unit :=
  newEvent'
  {
    guard m x := m.count + x ≤ ctx.maxCount
    action m x _ := {count := m.count + x}
    safety _ _ _ hgrd := hgrd

  }

def Two_Add_n : OrdinaryEvent (Bounded ctx) Nat Unit :=
  do
    Add_n
    Add_n

def exemple' : Bounded ({maxCount := 5, prop_maxCount := Nat.zero_lt_succ 4}) :=
  let i := Init.to_InitEvent.init (M := Bounded {maxCount := 5, prop_maxCount := Nat.zero_lt_succ 4} ) () (by trivial)
  i.2


#eval (Two_Add_n.action exemple' 2
  (
    by
      simp[Two_Add_n,exemple']
      simp [Bind.bind, Pure.pure]
      simp[Init]
      simp [bindEvent]
      simp[Add_n]
      simp [Bind.bind, Pure.pure]
      simp[bind_Event]
  )).2

-- def Bad_Seq : OrdinaryEvent (Bounded ctx) Nat Unit :=
--   do
--     Add_n
--     Incr

def Add_n' : OrdinaryEvent (Bounded ctx) Nat Nat :=
  newEvent
  {
    guard m x := m.count + x ≤ ctx.maxCount
    action m x _ := (x+1,{count := m.count + x})
    safety _ _ _ hgrd := hgrd
  }

def Add_n'' : OrdinaryEvent (Bounded ctx) Nat Nat :=
  newEvent
  {
    guard m x := m.count + x ≤ ctx.maxCount
    action m x _ := (x,{count := m.count + x})
    safety _ _ _ hgrd := hgrd
  }

def Sub_n' : OrdinaryEvent (Bounded ctx) Nat Nat :=
  newEvent
  {
    guard m x := m.count - x ≥ 0
    action m x _ := (x,{count := m.count - x})
    safety m x hinv hgrd :=
      by
        simp[Machine.invariant] at *
        exact Nat.le_add_right_of_le hinv
  }

def Add_Incr : OrdinaryEvent (Bounded ctx) Nat Unit :=
  Add_n (>>>) Incr

def Two_Add' : OrdinaryEvent (Bounded ctx) Nat Unit :=
  (Add_n') (>>>) Add_n


#eval (Add_Incr.action exemple' 2
  (
    by
      simp[Add_Incr]
      constructor
      · simp[Add_n,exemple',Init]
      · simp[Add_n,exemple',Incr,Init]
  )).2

#eval! (Two_Add'.action exemple' 3
  (
    by
      simp[Two_Add']
      constructor
      · simp[exemple',Init,Add_n']
      · simp[Add_n',exemple',Init,Add_n]
        -- Here we need to show false : it is never possible to give an argument for the guard
        -- when it is false, thus the action of the event can't be applied
        sorry
  )).2

def Add_l : OrdinaryEvent (Bounded ctx) (Nat × Nat) (Nat × Nat) :=
  StrongProfunctor.first' Add_n''

def Sub_r : OrdinaryEvent (Bounded ctx) (Nat × Nat) (Nat × Nat ) :=
  StrongProfunctor.second' Sub_n'

def Add_sub : OrdinaryEvent (Bounded ctx) (Nat × Nat) (Nat × Nat ) :=
  Add_l (>>>) Sub_r

#eval! (Add_sub.action exemple' (4,3) (by sorry)).2

def Final : OrdinaryEvent (Bounded ctx) (Nat × Nat) Nat :=
  (λ (x,y)=> x + y) <$> Add_sub

#eval! (Final.action exemple' (4,3) (by sorry)).1
