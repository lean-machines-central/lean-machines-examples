
import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary

namespace Bounded

structure BoundedCtx where
  maxCount : Nat

structure Bounded (ctx : BoundedCtx) where
  count : Nat

instance: Machine BoundedCtx (Bounded ctx) where
  context := ctx
  invariant := fun m => m.count ≤ ctx.maxCount
  reset := { count := 0 }

def Init : InitEvent (Bounded ctx) Unit Unit :=
  newInitEvent'' {
    init := { count := 0 }
    safety := fun _ => by simp [Machine.invariant]
  }

def Incr : OrdinaryEvent (Bounded ctx) Unit Unit :=
  newEvent'' {
    guard m := m.count < ctx.maxCount
    action m := { m with count := m.count + 1 }
    safety := fun m => by simp [Machine.invariant] ; intro _ Hgrd ; exact Hgrd
  }

def Decr : OrdinaryEvent (Bounded ctx) Unit Unit :=
  newEvent'' {
    guard m := m.count > 0
    action m := { m with count := m.count - 1 }
    safety := fun m => by simp [Machine.invariant] ; omega
  }

end Bounded
