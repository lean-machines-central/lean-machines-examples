
import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary

import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Defs.LinearOrder

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

instance: LE Clock where
  le ck₁ ck₂ := ck₁.val ≤ ck₂.val

@[simp]
theorem Clock_LE (ck₁ ck₂ : Clock):
  ck₁.val ≤ ck₂.val
  → ck₁ ≤ ck₂ :=
by
  intro Hval ; exact Hval

@[simp]
theorem Clock_LE_conv (ck₁ ck₂ : Clock):
  ck₁ ≤ ck₂
  → ck₁.val ≤ ck₂.val :=
by
  intro Hval ; exact Hval

instance: Preorder Clock where
  le_refl ck := by simp
  le_trans ck₁ ck₂ ck₃ := by
    intros H₁ H₂
    cases ck₁
    case mk v₁ =>
    cases ck₂
    case mk v₂ =>
    cases ck₃
    case mk v₃ =>
      apply Clock_LE
      simp
      exact Nat.le_trans H₁ H₂
  lt_iff_le_not_le ck₁ ck₂ := by
    cases ck₁
    case mk v₁ =>
    cases ck₂
    case mk v₂ =>
    constructor
    · intro H
      constructor
      · refine Clock_LE { val := v₁ } { val := v₂ } ?_
        exact Nat.le_of_succ_le H
      · intro Hcontra
        have H' : v₁ < v₂ := by exact H
        have Hcontra' : v₂ ≤ v₁ := by exact Hcontra
        have Hn : ¬ (v₁ < v₂) := by exact Nat.not_lt.mpr Hcontra
        contradiction
    · intro ⟨H₁, H₂⟩
      apply Clock_LT
      simp
      have H₁' : v₁ ≤ v₂ := by exact H₁
      have H₂' : ¬ (v₂ ≤ v₁) := by exact H₂
      exact Nat.gt_of_not_le H₂

instance: PartialOrder Clock where
  le_antisymm ck₁ ck₂ := by
    intros H₁ H₂
    cases ck₁
    case mk v₁ =>
    cases ck₂
    case mk v₂ =>
      simp
      have H₁' : v₁ ≤ v₂ := by exact H₁
      have H₂' : v₂ ≤ v₁ := by exact H₂
      exact Nat.le_antisymm H₁ H₂

instance: LinearOrder Clock where
  le_total ck₁ ck₂ := by
    cases ck₁
    case mk v₁ =>
    cases ck₂
    case mk v₂ =>
      show (v₁ ≤ v₂) ∨ (v₂ ≤ v₁)
      exact Nat.le_total v₁ v₂

  decidableLE := by
    simp [DecidableRel]
    intros ck₁ ck₂
    cases ck₁
    case mk v₁ =>
    cases ck₂
    case mk v₂ =>
      show Decidable (v₁ ≤ v₂)
      exact v₁.decLe v₂

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
