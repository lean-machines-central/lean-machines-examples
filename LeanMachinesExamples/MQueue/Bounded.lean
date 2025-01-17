
import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent
import LeanMachines.NonDet.Ordinary

structure BoundedCtx where
  maxCount : Nat
  prop_maxCount : Prop := maxCount > 0

structure Bounded (ctx : BoundedCtx) where
  count : Nat

namespace Bounded

instance: Machine BoundedCtx (Bounded ctx) where
  context := ctx
  invariant m := m.count ≤ ctx.maxCount
  default := { count := 0 }

def Init : InitEvent (Bounded ctx) Unit Unit :=
  newInitEvent'' {
    init _ := { count := 0 }
    safety _ := by simp [Machine.invariant]
  }

def Incr : OrdinaryEvent (Bounded ctx) Unit Unit :=
  newEvent'' {
    guard m := m.count < ctx.maxCount
    action m _ := { m with count := m.count + 1 }
    safety m := by simp [Machine.invariant]
                   intro Hinv Hgrd
                   exact Hgrd
  }

def Decr : ConvergentEvent Nat (Bounded ctx) Unit Unit :=
  newConvergentEvent'' {
    guard m := m.count > 0
    action m _ := { m with count := m.count - 1 }
    safety m := by simp [Machine.invariant] ; omega
    variant m := m.count
    convergence m := by simp; omega
  }

def Discard : OrdinaryNDEvent (Bounded ctx) Unit Nat :=
  newNDEvent {
    guard m _ := m.count > 0
    effect m _ grd := fun (k, m') =>
      ∃ k > 0, m' = {m with count := m.count - k}

    safety m _ := by
      simp [Machine.invariant]
      intros Hinv Hgrd m' k Hk Hm'
      simp [Hm']
      exact Nat.le_add_right_of_le Hinv

    feasibility m _ := by
      simp [Machine.invariant]
      intros Hinv Hgrd
      exists { count := m.count - 1}
      exists 1

  }

end Bounded
