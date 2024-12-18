import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Basic

import LeanMachines.Event.Ordinary

import LeanMachines.NonDet.Ordinary

namespace Prioritized

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
  lt p₁ p₂ := Ord.compare p₁ p₂ == Ordering.lt

instance: LE Prio where
  le p₁ p₂ := p₁ == p₂ ∨ Ord.compare p₁ p₂ == Ordering.lt

example: Prio.mk 3 < Prio.mk 4 := by rfl

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
    init := { priorities := ∅ }
    safety _ := by simp [Machine.invariant]
  }

def NewPrio : OrdinaryEvent (Prioritized ctx) Prio Unit :=
  newEvent' {
    guard m p := ctx.minPrio ≤ p ∧ p ≤ ctx.maxPrio ∧ p ∉ m.priorities
    action m p := { m with priorities := m.priorities ∪ {p} }
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
    action m p := { m with priorities := m.priorities \ {p} }
    safety m p := by
      simp [Machine.invariant]
      intros Hinv Hgrd₁ Hgrd₂ Hgrd₃ q Hq HHq
      exact Hinv q Hq
  }

end Prioritized
