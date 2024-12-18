
import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary

namespace Clocked

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
  lt ck₁ ck₂ := Ord.compare ck₁.val ck₂.val == Ordering.lt

@[simp]
theorem Clock_LT (ck₁ ck₂ : Clock):
  ck₁.val < ck₂.val
  → ck₁ < ck₂ :=
by
  -- XXX : longer than expected
  intro Hval
  simp [LT.lt, compare]
  unfold LT.lt at Hval
  unfold instLTNat at Hval
  simp at Hval
  unfold compareOfLessAndEq
  simp [Hval]
  rfl

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
