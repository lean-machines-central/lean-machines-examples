import Mathlib.Tactic

import LeanMachinesExamples.EventB.Bridge.Prelude
import LeanMachinesExamples.EventB.Bridge.Bridge0

import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.Convergent
import LeanMachines.Refinement.Relational.Concrete

/-!

## First refinement

In this first refinement, the total number of cars is
decomposed in three components (cf. below), illustrating
a simple form of data-refinement.

-/

namespace BridgeSpec

/-- The refined state (simple data-)-/
structure Bridge1 (ctx : Context) where
  /-- Number of cars on the bridge, coming from mainland and going towards the island. -/
  nbToIsland : Nat
  /-- Number of cars present on the island. -/
  nbOnIsland : Nat
  /-- Number of cars on the bridge, returning to mainland. -/
  nbFromIsland : Nat

@[simp]
def Bridge1.totalCars (b : Bridge1 ctx) := b.1 + b.2 + b.3

/-- First invariant: the total number of cars is less than the allowed maximum. -/
@[simp]
def Bridge1.invariant₁ (b : Bridge1 ctx) := b.totalCars ≤ ctx.maxCars

/-- Second invariant: crossing is forbidden on the bridge. -/
@[simp]
def Bridge1.invariant₂ (b : Bridge1 ctx) := b.nbFromIsland = 0 ∨ b.nbToIsland = 0

/-- Machine description of the first bridge refinement. -/
instance: Machine Context (Bridge1 ctx) where
  context := ctx
  invariant b := b.invariant₁ ∧ b.invariant₂
  reset := ⟨0, 0, 0⟩

/-- The refine (a.k.a "glue") invariant connecting the concrete bridge
to the abstract one. -/
@[simp]
def Bridge1.refine (b0 : Bridge0 ctx) (b1 : Bridge1 ctx) : Prop :=
  b1.totalCars = b0.nbCars

/-- Proof obligation:  correct machine refinement
(cf. `Refinement.refine_safe`). -/
instance: Refinement (Bridge0 ctx) (Bridge1 ctx) where
  refine := Bridge1.refine
  refine_safe := fun b0 b1 => by
    simp [Machine.invariant]
    intros Hinv₁ _ Href
    simp [Hinv₁, ←Href]

/- Remark: We de not exploit this (by using a functional variant
 of refinement), but this is an interesting property anyway. -/
theorem Bridge1.refine_uniq (b1 : Bridge1 ctx) (b0a b0b : Bridge0 ctx):
    Machine.invariant b1
    → Refinement.refine b0a b1 → Refinement.refine (M:=Bridge1 ctx) b0b b1
    → b0a = b0b :=
by
  simp [Machine.invariant, Refinement.refine]
  intros Hinv₁ _ Href Href'
  simp [*] at *
  cases b1
  case mk _ =>
    simp at *
    cases b0b
    case mk nb' =>
      simp at Href
      simp [Href]

namespace Bridge1

/-- Initialization event: empty bridge (refinement of `Bridge0.Init`). -/
def Init : InitREvent (Bridge0 ctx) (Bridge1 ctx) Unit Unit :=
  newInitREvent'' Bridge0.Init {
    init := ⟨0, 0, 0⟩
    safety := by simp [Machine.invariant]
    strengthening := by simp [Bridge0.Init]
    simulation := by simp [Bridge0.Init, Refinement.refine]
  }

/-- Event: entering from mainland (refinement of `Bridge0.EnterFromMainland`). -/
def EnterFromMainland : OrdinaryREvent (Bridge0 ctx) (Bridge1 ctx) Unit Unit :=
  newREvent'' Bridge0.EnterFromMainland {
    guard := fun b1 => b1.totalCars < ctx.maxCars ∧ b1.nbFromIsland = 0
    action := fun b1 => { b1 with nbToIsland := b1.nbToIsland + 1 }
    safety := fun b1 => by
      simp [Machine.invariant]
      intros _ _ Hgrd₁ Hgrd₂
      constructor
      · simp_arith
        exact Hgrd₁
      · assumption
    strengthening := fun b1 => by
      simp [Machine.invariant, Refinement.refine, Bridge0.EnterFromMainland, newEvent']
      intros _ _ Hgd₁ _ b0 Href
      exact Eq.trans_lt (id Href.symm) Hgd₁
    simulation := fun b1 => by
      simp [Machine.invariant, Refinement.refine, Bridge0.EnterFromMainland, newEvent']
      intros _ _ _ _ b0 Href
      simp_arith
      exact Href
  }

/-- Event: leaving to mainland (refinement of `Bridge0.LeaveToMainland`). -/
def LeaveToMainland : OrdinaryREvent (Bridge0 ctx) (Bridge1 ctx) Unit Unit :=
  newREvent'' Bridge0.LeaveToMainland {
    guard := fun b1 => b1.nbFromIsland > 0
    action := fun b1 => { b1 with nbFromIsland := b1.nbFromIsland - 1 }
    safety := fun b1 => by
      simp [Machine.invariant]
      intros Hinv₁ Hinv₂ Hgrd
      cases Hinv₂
      case inl Hinv₂ =>
        linarith
      case inr Hinv₂ =>
        simp [Hinv₂]
        simp [Hinv₂] at Hinv₁
        rw [← Nat.add_sub_assoc]
        · simp_arith [Hinv₁]
          exact Nat.le_step Hinv₁
        · exact Hgrd
    strengthening := fun b1 => by
      simp [Machine.invariant, Refinement.refine, Bridge0.LeaveToMainland, newEvent']
      intros _ _ Hgrd b0 Href
      linarith
    simulation := fun b1 => by
      simp [Machine.invariant, Refinement.refine, Bridge0.LeaveToMainland, newEvent']
      intros _ _ Hgrd b0 Href
      rw [← Nat.add_sub_assoc]
      · rw [←Href]
      · exact Hgrd
  }

/-- Concrete event: entering the island.
The event refines the abstract `Skip` and is demonstrated convergent.

Remark: although Event-B prescribes convergence for concrete events, this
is not enforced in LeanMachines (cf. discussion in the framework implementation).
-/
def EnterIsland : ConvergentRDetEvent Nat (Bridge0 ctx) (Bridge1 ctx) Unit Unit :=
  newConcreteConvergentREvent'' {
    guard := fun b1 => b1.nbToIsland > 0
    action := fun b1 => ⟨b1.nbToIsland - 1, b1.nbOnIsland + 1, b1.nbFromIsland⟩
    safety := fun b1 => by
      simp [Machine.invariant]
      intros Hinv₁ Hinv₂ Hgrd
      constructor
      ·  rw [Nat_sub_add_comm_cancel]
         · assumption
         · exact Hgrd
      · cases Hinv₂
        case right.inl Hinv₂ => exact Or.inl Hinv₂
        case right.inr Hinv₂ =>
          apply Or.intro_right
          simp [Hinv₂]
    variant := fun b1 => b1.nbToIsland
    convergence := fun b1 => by
      simp [Machine.invariant]

    simulation := fun b1 => by
      simp [Machine.invariant, Refinement.refine]
      intros _ _ Hgrd b0 Href
      rw [Nat_sub_add_comm_cancel]
      · assumption
      · exact Hgrd
  }

/-- Concrete event: leaving the island. -/
def LeaveIsland : ConvergentRDetEvent Nat (Bridge0 ctx) (Bridge1 ctx) Unit Unit :=
  newConcreteConvergentREvent'' {
    guard := fun b1 => b1.nbOnIsland > 0 ∧ b1.nbToIsland = 0
    action := fun b1 => ⟨b1.nbToIsland, b1.nbOnIsland - 1, b1.nbFromIsland + 1⟩
    safety := fun b1 => by
      simp [Machine.invariant]
      intros Hinv₁ _ Hgrd₁ Hgrd₂
      simp [Hgrd₂] at Hinv₁
      simp [Hgrd₂]
      have Hgoal : b1.nbOnIsland - 1 + (b1.nbFromIsland + 1)
                   = b1.nbOnIsland - 1 + 1 + b1.nbFromIsland := by
        simp_arith
      rw [Hgoal] ; clear Hgoal
      rw [Nat.sub_add_cancel Hgrd₁]
      assumption
    variant := fun b1 => b1.nbOnIsland
    convergence := fun b1 => by
      simp [Machine.invariant]
      intros _ _ Hgrd₁ _
      exact Hgrd₁
    simulation := fun b1 => by
      simp [Machine.invariant, Refinement.refine]
      intros _ _ Hgrd₁ Hgrd₂ b0 Href
      simp [Hgrd₂]
      rw [Nat.add_left_comm]
      rw [Nat.sub_add_cancel Hgrd₁]
      simp [Hgrd₂] at Href
      rw [←Href]
      simp_arith
  }

/-- Machine Property : deadlock freedom -/
theorem deadlockFreedom (m : Bridge1 ctx):
  Machine.invariant m
  → EnterFromMainland.guard m () ∨ LeaveToMainland.guard m ()
    ∨ EnterIsland.guard m () ∨ LeaveIsland.guard m () :=
by
  simp [Machine.invariant, EnterFromMainland, LeaveToMainland, EnterIsland, LeaveIsland]
  intro Hinv₁ Hinv₂
  have Hctx := ctx.maxCars_pos
  cases Hinv₂
  case inl Hinv₂ =>
    simp [Hinv₂] ; simp [Hinv₂] at Hinv₁
    have H₁: m.nbToIsland + m.nbOnIsland < ctx.maxCars
             ∨ m.nbToIsland + m.nbOnIsland = ctx.maxCars := by
      apply Nat.lt_or_eq_of_le
      assumption
    cases H₁
    case inl H₁ => simp [H₁]
    case inr H₁ =>
      apply Or.intro_right
      by_cases m.nbToIsland = 0
      case pos H₂ =>
        simp [H₂]
        simp [H₂] at H₁
        exact Nat.lt_of_lt_of_eq Hctx (id H₁.symm)
      case neg H₂ =>
        apply Or.intro_left
        exact Nat.pos_of_ne_zero H₂
  case inr Hinv₂ =>
    simp [Hinv₂] ; simp [Hinv₂] at Hinv₁
    by_cases m.nbFromIsland = 0
    case pos H₁ =>
      simp [H₁] ; simp [H₁] at Hinv₁
      have H₂: m.nbOnIsland < ctx.maxCars
             ∨ m.nbOnIsland = ctx.maxCars := by
        apply Nat.lt_or_eq_of_le
        assumption
      cases H₂
      case inl H₂ => simp [H₂]
      case inr H₂ =>
        apply Or.intro_right
        exact Nat.lt_of_lt_of_eq Hctx (id H₂.symm)
    case neg H₁ =>
      simp [H₁]
      left
      exact Nat.pos_of_ne_zero H₁


end Bridge1

end BridgeSpec
