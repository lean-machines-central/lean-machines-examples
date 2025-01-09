import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Basic

import LeanMachines.Event.Ordinary

import LeanMachines.NonDet.Ordinary

namespace Prioritized

@[ext]
structure Prio where
  prio : Nat
deriving Repr, BEq, DecidableEq

instance: OfNat Prio n where
  ofNat := {prio := n}

example: Prio.mk 4 = 4 := by rfl

instance: Coe Prio Nat where
  coe := fun {prio:=p} => p

instance: LawfulBEq Prio where
  eq_of_beq := by intros p₁ p₂ Hbeq
                  cases p₁
                  case mk prio₁ =>
                  cases p₂
                  case mk prio₂ =>
                    have Heq : prio₁ = prio₂ := by
                      apply eq_of_beq
                      exact Hbeq
                    simp [Heq]
  rfl := by intro p
            cases p
            case mk n =>
              apply beq_self_eq_true'

instance: Ord Prio where
  compare p₁ p₂ := compare p₁.prio p₂.prio

instance: LT Prio where
  lt p₁ p₂ := p₁.prio < p₂.prio

@[simp]
theorem Prio_lift_lt (p₁ p₂ : Prio):
  p₁.prio < p₂.prio
  → p₁ < p₂ :=
by
  intro H ; exact H

theorem Prio_unlift_lt (p₁ p₂ : Prio):
  p₁ < p₂
  → p₁.prio < p₂.prio :=
by
  intro H ; exact H

example: Prio.mk 3 < Prio.mk 4 := by
  apply Prio_lift_lt
  apply Nat.lt_add_one

instance: LE Prio where
  le p₁ p₂ := p₁.prio ≤ p₂.prio

@[simp]
theorem Prio_lift_le (p₁ p₂ : Prio):
  p₁.prio ≤ p₂.prio
  → p₁ ≤ p₂ :=
by
  intro H ; exact H

theorem Prio_unlift_le (p₁ p₂ : Prio):
  p₁ ≤ p₂
  → p₁.prio ≤ p₂.prio :=
by
  intro H ; exact H

example: Prio.mk 3 ≤ Prio.mk (2 + 1) := by
  apply Prio_lift_lt
  apply Nat.lt_add_one

instance: Preorder Prio where
  le_refl := fun p => by simp
  le_trans := fun p₁ p₂ p₃ => by
    intros H₁ H₂
    apply Prio_lift_le
    exact Nat.le_trans H₁ H₂
  lt_iff_le_not_le := fun ⟨p₁⟩ ⟨p₂⟩ => by
    constructor
    case mp =>
      intro H
      constructor
      case left =>
        apply Prio_lift_le
        exact Nat.le_of_succ_le H
      case right =>
        intro Hcontra
        have H' : p₁ < p₂ := H
        have Hcontra' : p₂ ≤ p₁ := Hcontra
        omega
    case mpr =>
      intro ⟨H₁,H₂⟩
      have H₁' : p₁ ≤ p₂ := H₁
      have H₂' : ¬ (p₂ ≤ p₁) := H₂
      apply Prio_lift_le
      simp
      omega

instance: PartialOrder Prio where
  le_antisymm := fun ⟨p₁⟩ ⟨p₂⟩ => by
    intros H₁ H₂
    apply Prio.ext
    exact Nat.le_antisymm H₁ H₂

instance (p₁ p₂ : Prio): Decidable (p₁ ≤ p₂) := inferInstance
instance (p₁ p₂ : Prio): Decidable (p₁ < p₂) := inferInstance
instance (p₁ p₂ : Prio): Decidable (p₁ = p₂) := inferInstance

instance: Max Prio where
  max p₁ p₂ := ⟨max p₁.prio p₂.prio⟩

instance: Min Prio where
  min p₁ p₂ := ⟨min p₁.prio p₂.prio⟩

instance: LinearOrder Prio where
  le_total p₁ p₂ := by apply Nat.le_total
  decidableLE := inferInstance --instDecidableLePrio
  min_def p₁ p₂ := by exact apply_ite Prio.mk (p₁.prio ≤ p₂.prio) p₁.prio p₂.prio
  max_def p₁ p₂  := by exact apply_ite Prio.mk (p₁.prio ≤ p₂.prio) p₂.prio p₁.prio
  compare_eq_compareOfLessAndEq p₁ p₂ := by
    simp [compare]
    cases p₁
    case mk prio₁ =>
    cases p₂
    case mk prio₂ =>
      simp [compareOfLessAndEq]
      rfl

structure PrioCtx where
  minPrio : Prio
  maxPrio : Prio
  minMaxOrd : minPrio < maxPrio

set_option linter.dupNamespace false

structure Prioritized (ctx : PrioCtx) where
  priorities : Finset Prio

instance: Machine PrioCtx (Prioritized ctx) where
  context := ctx
  invariant := fun m => ∀ p ∈ m.priorities, ctx.minPrio ≤ p ∧ p ≤ ctx.maxPrio
  reset := { priorities := ∅ }

def Init : InitEvent (Prioritized ctx) Unit Unit :=
  newInitEvent'' {
    init _ := { priorities := ∅ }
    safety _ := by simp [Machine.invariant]
  }

def NewPrio : OrdinaryEvent (Prioritized ctx) Prio Unit :=
  newEvent' {
    guard m p := ctx.minPrio ≤ p ∧ p ≤ ctx.maxPrio ∧ p ∉ m.priorities
    action m p _ := { m with priorities := m.priorities ∪ {p} }
    safety m p := by
      simp [Machine.invariant]
      intros Hinv Hgrd₁ Hgrd₂ Hgrd₃ q Hq
      cases Hq
      case inl Hq =>
        exact Hinv q Hq
      case inr Hq =>
        rw [Hq]
        exact ⟨Hgrd₁, Hgrd₂⟩
  }

def DelPrio : OrdinaryEvent (Prioritized ctx) Prio Unit :=
  newEvent' {
    guard m p := ctx.minPrio ≤ p ∧ p ≤ ctx.maxPrio ∧ p ∈ m.priorities
    action m p _ := { m with priorities := m.priorities \ {p} }
    safety m p := by
      simp [Machine.invariant]
      intros Hinv Hgrd₁ Hgrd₂ Hgrd₃ q Hq HHq
      exact Hinv q Hq
  }

end Prioritized
