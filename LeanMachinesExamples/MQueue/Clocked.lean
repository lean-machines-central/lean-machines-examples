
import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary

namespace Clocked

@[ext]
structure Clock where
  val : Nat
deriving Repr, BEq, DecidableEq

instance: OfNat Clock n where
  ofNat := {val := n}

example: Clock.mk 4 = 4 := by rfl

instance: Coe Clock Nat where
  coe := fun {val:=p} => p

instance: Add Clock where
  add ck₁ ck₂ := {val:=ck₁.val + ck₂.val}

instance: LT Clock where
  lt ck₁ ck₂ := ck₁.val < ck₂.val

@[simp]
theorem Clock_LT (ck₁ ck₂ : Clock):
  ck₁.val < ck₂.val
  → ck₁ < ck₂ :=
by
  intro Hval ; exact Hval

@[simp]
theorem Clock_LT_conv (ck₁ ck₂ : Clock):
  ck₁ < ck₂
  → ck₁.val < ck₂.val :=
by
  intro Hval ; exact Hval

structure EmptyCtx where

structure Clocked where
  clock : Clock

instance: Machine EmptyCtx Clocked where
  context := {}
  invariant := fun _ => True
  reset := { clock := 0 }

def Init : InitEvent Clocked Unit Unit :=
  newInitEvent'' {
    init := { clock := 0 }
    safety := fun _ => by simp [Machine.invariant]
  }

def Tick : OrdinaryEvent Clocked Unit Unit :=
  newEvent'' {
    action m := { m with clock := m.clock + 1 }
    safety := fun m => by simp [Machine.invariant]
  }

end Clocked
