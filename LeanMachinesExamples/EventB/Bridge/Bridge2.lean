
import Mathlib.Tactic

import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.Convergent
import LeanMachines.Refinement.Relational.Abstract

import LeanMachinesExamples.EventB.Bridge.Bridge1

/-!

## Second refinement

In the second refinement, traffic lights are specified.
This is an example of a superposition refinement
(since the varialbes from the first refinement are preserved).

-/


namespace BridgeSpec

/-- Traffic light colors. -/
inductive Color where | Green | Red
  deriving Repr, BEq, DecidableEq

/-- The state of the second Bridge refinement.
Note that this *extends* the first refinement state
(=> superposition). -/
structure Bridge2 (ctx : Context) extends (Bridge1 ctx) where
  /-- Traffic light: from mainland. -/
  mainlandTL : Color
  /-- A flag to allow/disallow cars entering from mainland. -/
  mainlandPass : Bool
  /-- Traffic light: from island. -/
  islandTL : Color
  /-- A flag to allow/disallow cars entering from the island. -/
  islandPass : Bool

/-- Invariant: constraints when mainland trafic light is green. -/
def Bridge2.invariant₁ (b : Bridge2 ctx) :=
  b.mainlandTL = Color.Green
  →  b.toBridge1.nbToIsland + b.toBridge1.nbOnIsland < ctx.maxCars
     ∧ b.toBridge1.nbFromIsland = 0

/-- Invariant: constraints when island traffic light is green. -/
def Bridge2.invariant₂ (b : Bridge2 ctx) :=
  b.islandTL = Color.Green
  → b.nbOnIsland > 0 ∧ b.nbToIsland = 0

/-- Invariant: at any time at least one traffic light is red. -/
def Bridge2.invariant₃ (b : Bridge2 ctx) :=
  b.islandTL = Color.Red ∨ b.mainlandTL = Color.Red

/-- Invariant: enabling mainland pass. -/
def Bridge2.invariant₄ (b : Bridge2 ctx) :=
  b.mainlandTL = Color.Red → b.mainlandPass = true

/-- Invariant: enabling island pass. -/
def Bridge2.invariant₅ (b : Bridge2 ctx) :=
  b.islandTL = Color.Red → b.islandPass = true

/-- Refine invariant-/
def Bridge2.refine (b1 : Bridge1 ctx) (b2 : Bridge2 ctx) :=
  b2.toBridge1 = b1 -- this is a superposition

/-- The machine specification of the second bridge refinement. -/
instance: Machine Context (Bridge2 ctx) where
  context := ctx
  invariant b := Bridge2.invariant₁ b ∧ Bridge2.invariant₂ b ∧ Bridge2.invariant₃ b
                 ∧ Bridge2.invariant₄ b ∧ Bridge2.invariant₅ b
                 ∧ Machine.invariant b.toBridge1
                   -- this is handy in case of superposition, instead of putting the
                   -- glue in the refine predicate
  default := let r1 : Bridge1 ctx := default
           { r1 with mainlandTL := Color.Red
                     mainlandPass := false
                     islandTL := Color.Red
                     islandPass := false }

/-- Proof obligation: correct machine refinement. -/
instance: Refinement (Bridge1 ctx) (Bridge2 ctx) where
  refine := Bridge2.refine
  refine_safe := fun b1 b2 => by
    simp [Bridge2.refine] -- trivial in case of superposition
    intros Hinv Href
    simp [Machine.invariant] at *
    simp [←Href, Hinv]

namespace Bridge2

theorem refine_uniq (b1a b1b : Bridge1 ctx) (b2 : Bridge2 ctx):
    Machine.invariant b2
    → refine b1a b2 → refine b1b b2
    → b1a = b1b :=
by
  simp [Bridge2.refine]
  intros _ Href Href'
  rw [←Href, ←Href']

/-- Initialization event: empty bridge (refinement of `Bridge1.Init`). -/
def Init : InitREvent (Bridge1 ctx) (Bridge2 ctx) Unit Unit :=
  newInitREvent'' Bridge1.Init.toInitEvent {
    init _ := let b1 : Bridge1 ctx := (Bridge1.Init.init () (by simp [Bridge1.Init])).2
              { b1  with mainlandTL := Color.Green , islandTL := Color.Red,
                         mainlandPass := false, islandPass := true }
    safety := by
      simp [Machine.invariant, invariant₁, invariant₂, invariant₃, invariant₄, invariant₅]
      simp [Bridge1.Init]
      simp [ctx.maxCars_pos]
    strengthening := by simp [Bridge1.Init, newInitEvent']
    simulation := by
      simp [Bridge1.Init, newInitEvent', Refinement.refine, Bridge2.refine, Machine.invariant]
  }

/-- Event: entering from mainland (refinement of `Bridge1.EnterFromMainland`).
This is the first event of a two-part decomposition of the action, which illustrates
*decomposability* of refined events, a powerful feature of Event-B.
 -/
def EnterFromMainland₁ : OrdinaryREvent (Bridge1 ctx) (Bridge2 ctx) Unit Unit :=
  newREvent'' Bridge1.EnterFromMainland.toOrdinaryEvent {
    guard := fun b2 => b2.mainlandTL = Color.Green ∧ b2.nbOnIsland + b2.nbToIsland + 1 ≠ ctx.maxCars

    action := fun b2 _ => { b2 with nbToIsland := b2.nbToIsland + 1
                                    mainlandPass := true }
    safety := fun b2 => by
      simp [Machine.invariant, invariant₁, invariant₂, invariant₃, invariant₄, invariant₅]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv₆ Hinv₇ Hgrd₁ Hgrd₂
      simp [Hgrd₁] at *
      simp [Hinv₃] at *
      simp [Hinv₅]
      cases Hinv₁
      case intro Hinv₁ Hinv₁' =>
        simp [Hinv₁'] at *

        have Hleft: b2.nbToIsland + 1 + b2.nbOnIsland < ctx.maxCars := by
          have H₁ : b2.nbToIsland + 1 + b2.nbOnIsland
                    = b2.nbToIsland + b2.nbOnIsland + 1 := by simp_arith
          rw [H₁] ; clear H₁
          apply Nat.lt_of_le_of_ne
          · exact Hinv₁
          · conv => pattern b2.nbToIsland + b2.nbOnIsland
                    rw [Nat.add_comm]
            exact Hgrd₂
        simp [Hleft]
        exact Nat.le_of_lt Hleft

    strengthening := fun b2 => by
      simp [Bridge1.EnterFromMainland, Refinement.refine, Bridge2.refine, Machine.invariant, invariant₁, invariant₂, invariant₃, invariant₄, invariant₅]
      intros Hinv₁ _ Hinv₃ _ _ _ _ Hgrd₁ _
      simp [Hgrd₁, Hinv₃, Hinv₁]

    simulation := fun b2 => by
      simp [Machine.invariant, Refinement.refine, Bridge2.refine, Bridge1.EnterFromMainland]

  }

/-- Event: entering from mainland (refinement of `Bridge1.EnterFromMainland`).
This is the second event of a two-part decomposition of the action.
 -/
def EnterFromMainland₂ : OrdinaryREvent (Bridge1 ctx) (Bridge2 ctx) Unit Unit :=
  newREvent'' Bridge1.EnterFromMainland.toOrdinaryEvent {
    guard := fun b2 => b2.mainlandTL = Color.Green ∧ b2.nbOnIsland + b2.nbToIsland + 1 = ctx.maxCars
    action := fun b2 _ => { b2 with nbToIsland := b2.nbToIsland + 1
                                    mainlandTL := Color.Red
                                    mainlandPass := true }

    safety := fun b2 => by simp [Machine.invariant, invariant₁, invariant₂, invariant₃, invariant₄, invariant₅]
                           intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv₆ Hinv₇ Hgrd₁ Hgrd₂
                           simp [Hgrd₁] at *
                           simp [Hinv₃, Hinv₅, Hinv₁] at *
                           rw [←Hgrd₂]
                           simp_arith

    strengthening := fun b2 => by simp [Bridge1.EnterFromMainland, Refinement.refine, Bridge2.refine, Machine.invariant, invariant₁, invariant₂, invariant₃, invariant₄, invariant₅]
                                  intros Hinv₁ _ Hinv₃ _ _ _ _ Hgrd₁ _
                                  simp [Hgrd₁, Hinv₃, Hinv₁]

    simulation := fun b2 => by simp [Machine.invariant, Refinement.refine, Bridge2.refine, Bridge1.EnterFromMainland, invariant₁, invariant₂, invariant₃, invariant₄, invariant₅]

  }

/-!

We now illustrate an important, although somewhat underemphasized, aspect of Event-B:
 the reuse of abstract events.
Because an abstract event doesn't "know" the concrete state, it can be difficult
to reuse directly the abstract specification at the concrete level.
Of course, as far as superposition is concerned, this is less of a problem
 since the stricly-concrete part of the state should be left untouched.
The LeanMachines framework introduces a notion of *strong* functional refinement
 for this purpose, which enables the straightforward reuse of abstract events
  in situations such as (but not limited to) superposition.
Here, we use the classical relational refinement, hence the proof obligations are
less trivial  (in fact, this is a local variant of strong functional refinement).

-/

@[simp]
def lift (b2 : Bridge2 ctx) : Bridge1 ctx :=
  b2.toBridge1

theorem lift_ref (b2 : Bridge2 ctx):
  Machine.invariant b2 → refine (lift b2) b2 :=
by
  simp [refine]

@[simp]
def unlift (b1 : Bridge1 ctx) (b2 : Bridge2 ctx) : Bridge2 ctx :=
  { b2 with toBridge1 := b1}

/-- Event: leaving the bridge  (refinement of `Bridge1.LeaveToMainland`).
Most of the abstract event specification is reused.
-/
def LeaveToMainland : OrdinaryREvent (Bridge1 ctx) (Bridge2 ctx) Unit Unit :=
  newAbstractREvent Bridge1.LeaveToMainland.toOrdinaryEvent {
    lift := lift
    lift_ref := lift_ref
    refine_uniq := refine_uniq
    unlift := fun _ b1' b2 _ => unlift b1' b2
    step_ref := fun b2 x => by simp [Refinement.refine, refine]
    step_safe := fun b2 x =>   by
      simp
      intros Hinv Hgrd
      have Hainv := Refinement.refine_safe b2.toBridge1 b2 Hinv rfl
      have Hsafe:= Bridge1.LeaveToMainland.toOrdinaryEvent.po.safety b2.toBridge1 x Hainv Hgrd
      simp [Bridge1.LeaveToMainland, Machine.invariant
            , invariant₁, invariant₂, invariant₃, invariant₄, invariant₅] at *
      obtain ⟨Hinv₁, Hinv₂, Hinv₃, Hinv₄, Hinv₅, Hinv₆⟩ := Hinv
      simp [*] at *
      cases Hinv₃
      case inl Hinv₃ =>
        simp [*] at *
        have Hcut: b2.mainlandTL = Color.Green ∨ b2.mainlandTL = Color.Red := by
          cases b2.mainlandTL <;> trivial
        cases Hcut <;> simp [*]
      case inr Hinv₃ =>
        simp [*] at *
        have Hcut: b2.islandTL = Color.Green ∨ b2.islandTL = Color.Red := by
          cases b2.islandTL <;> trivial
        cases Hcut <;> simp [*]
      /- remark : this would roughly the proof needed for machine-level refinement. -/

  }

/-- Event: entering the island  (refinement of `Bridge1.EnterIsland`).
Most of the abstract event specification is reused.
-/
def EnterIsland : ConvergentREvent Nat (Bridge1 ctx) (Bridge2 ctx) Unit Unit :=
  newAbstractConvergentREvent Bridge1.EnterIsland.toConvergentEvent {
    lift := lift
    lift_ref := lift_ref
    refine_uniq := refine_uniq
    unlift := fun _ b1' b2 _ => unlift b1' b2
    step_ref := fun b2 x => by simp [Refinement.refine, refine]
    step_safe := fun b2 x =>   by
      /- Remark: this proof is quite redundant with the one for `LeaveIsland`. -/
      simp
      intros Hinv Hgrd
      have Hainv := Refinement.refine_safe b2.toBridge1 b2 Hinv rfl
      have Hsafe:= Bridge1.EnterIsland.po.safety b2.toBridge1 x Hainv Hgrd
      simp [Bridge1.EnterIsland, Machine.invariant
           , invariant₁, invariant₂, invariant₃, invariant₄, invariant₅] at *
      obtain ⟨Hinv₁, Hinv₂, Hinv₃, Hinv₄, Hinv₅, Hinv₆⟩ := Hinv
      simp [*] at *
      cases Hinv₃
      case inl Hinv₃ =>
        simp [*] at *
        have Hcut: b2.mainlandTL = Color.Green ∨ b2.mainlandTL = Color.Red := by
          cases b2.mainlandTL <;> trivial
        cases Hcut
        case inl Hcut =>
          simp [*] at *
          have Hcalc := by calc  b2.nbToIsland - 1 + (b2.nbOnIsland + 1) = b2.nbToIsland - 1 + 1  + b2.nbOnIsland := by simp_arith
                                 _ =   b2.nbToIsland + b2.nbOnIsland := by rw [Nat.sub_add_cancel]
                                                                           exact Hgrd
          rw [Hcalc]
          simp [Hinv₁]
        case inr Hcut =>
          simp [*] at *
      case inr Hinv₃ =>
        simp [*] at *
        have Hcut: b2.islandTL = Color.Green ∨ b2.islandTL = Color.Red := by
          cases b2.islandTL <;> trivial
        cases Hcut
        case inl Hcut =>
          simp [*] at *
        case inr Hcut =>
          simp [*] at *
    step_variant := fun b2 _ => by simp
  }


/- Event: leaving island (decomposed, part 1), refinement of `Bridge1.LeaveIsland`. -/
def LeaveIsland₁ : ConvergentREvent Nat (Bridge1 ctx) (Bridge2 ctx) Unit Unit :=
  newConvergentREvent'' Bridge1.LeaveIsland.toConvergentEvent.toAnticipatedEvent.toOrdinaryEvent {
    guard := fun b2 => b2.islandTL = Color.Green ∧ b2.nbOnIsland ≠ 1

    action := fun b2 _ => { b2 with nbFromIsland := b2.nbFromIsland + 1
                                    nbOnIsland := b2.nbOnIsland - 1
                                    islandPass := true }

    safety := fun b2 => by
      simp [Machine.invariant, invariant₁, invariant₂, invariant₃, invariant₄, invariant₅]
      rintro Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv₆ Hinv₇ Hgrd₁ Hgrd₂
      simp [*] at *
      have Hml: b2.mainlandTL = Color.Green ∨ b2.mainlandTL = Color.Red := by
        cases b2.mainlandTL <;> trivial
      cases Hml
      case inl Hml =>
        simp [*] at *
      case inr Hml =>
        simp [*] at *
        constructor
        · apply Nat.lt_of_le_of_ne
          · apply Nat.le_of_pred_lt ; simp_arith [Hinv₂]
          · exact Ne.symm Hgrd₂
        · rw [Nat_sub_add_comm_cancel]
          · assumption
          · apply Nat.le_of_pred_lt ; simp_arith [Hinv₂.1]

    variant := fun b2 => Bridge1.LeaveIsland.po.variant b2.toBridge1

    convergence := fun b2 => by
      simp
      intros Hinv Hgrd₁ _
      simp [Bridge1.LeaveIsland]
      simp [Machine.invariant, invariant₂] at Hinv
      simp [*] at *

    strengthening := fun b2 => by
      simp
      intro Hinv Hgrd₁ _
      simp [Refinement.refine, refine, Bridge1.LeaveIsland]
      simp [Machine.invariant, invariant₂] at Hinv
      simp [Hinv, Hgrd₁]

    simulation := fun b2 => by
      simp
      intros _ _  am
      simp [Refinement.refine, refine, Bridge1.LeaveIsland]
      intro Href
      simp [←Href] at *
  }

/- Event: leaving island (decomposed, part 2), refinement of `Bridge1.LeaveIsland`. -/
def LeaveIsland₂ : ConvergentREvent Nat (Bridge1 ctx) (Bridge2 ctx) Unit Unit :=
  newConvergentREvent'' Bridge1.LeaveIsland.toConvergentEvent.toAnticipatedEvent.toOrdinaryEvent {
    guard := fun b2 => b2.islandTL = Color.Green ∧ b2.nbOnIsland = 1

    action := fun b2 _ => { b2 with nbFromIsland := b2.nbFromIsland + 1
                                    nbOnIsland := b2.nbOnIsland - 1
                                    islandTL := Color.Red
                                    islandPass := true }

    safety := fun b2 => by
      simp [Machine.invariant, invariant₁, invariant₂, invariant₃, invariant₄, invariant₅]
      intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv₆ Hinv₇ Hgrd₁ Hgrd₂
      simp [*] at *
      have Hml: b2.mainlandTL = Color.Green ∨ b2.mainlandTL = Color.Red := by
        cases b2.mainlandTL <;> trivial
      cases Hml
      case inl Hml =>
        simp [*] at *
      case inr Hml =>
        simp [*] at *
        rw [Nat.add_comm]
        assumption

    variant := fun b2 => Bridge1.LeaveIsland.po.variant b2.toBridge1

    convergence := fun b2 => by
      simp
      intros Hinv _ Hgrd₂
      simp [Bridge1.LeaveIsland]
      simp [Machine.invariant, invariant₂] at Hinv
      simp [*] at *

    strengthening := fun b2 => by
      simp
      intro Hinv Hgrd₁ _
      simp [Refinement.refine, refine, Bridge1.LeaveIsland]
      simp [Machine.invariant, invariant₂] at Hinv
      simp [Hinv, Hgrd₁]

    simulation := fun b2 => by
      simp
      intros _ _ am
      simp [Refinement.refine, refine, Bridge1.LeaveIsland]
      intro Href
      simp [←Href] at *

  }


@[simp]
def bval (b : Bool) : Nat :=
  match b with
  | false => 0
  | true => 1

/-- Event:  mainland traffic light goes green  (concrete convergent event). -/
def MailandTLGreen : ConvergentRDetEvent Nat (Bridge1 ctx) (Bridge2 ctx) Unit Unit :=
  newConcreteConvergentREvent'' {
    guard := fun b2 => b2.mainlandTL = Color.Red ∧ b2.nbToIsland + b2.nbOnIsland < ctx.maxCars ∧ b2.nbFromIsland = 0 ∧ b2.islandPass = true

    action := fun b2 _ => { b2 with mainlandTL := Color.Green
                                    islandTL := Color.Red
                                    mainlandPass := false }

    safety := fun b2 => by
      simp [Machine.invariant, invariant₁, invariant₂, invariant₃, invariant₄, invariant₅]
      intros Hinv₁ _ Hinv₃ Hinv₄ Hinv₅ Hinv₆ Hinv₇ Hgrd₁ Hgrd₂ Hgrd₃ Hgrd₄
      simp [*] at *
      assumption

    variant := fun b2 => (bval b2.mainlandPass) + (bval b2.islandPass)

    convergence := fun b2 => by
      simp
      intros Hinv Hgrd₁ _ _ _
      simp [Machine.invariant, invariant₄] at Hinv
      simp [Hgrd₁] at Hinv
      simp [Hinv]

    simulation := fun b2 => by simp [Refinement.refine, refine]
  }

/-- Event:  mainland traffic light goes green  (concrete convergent event). -/
def IslandTLGreen : ConvergentRDetEvent Nat (Bridge1 ctx) (Bridge2 ctx) Unit Unit :=
  newConcreteConvergentREvent'' {
    guard := fun b2 => b2.islandTL = Color.Red ∧ b2.nbOnIsland > 0 ∧ b2.nbToIsland = 0 ∧ b2.mainlandPass = true

    action := fun b2 _ => { b2 with mainlandTL := Color.Red
                                    islandTL := Color.Green
                                    islandPass := false }

    safety := fun b2 => by
      simp [Machine.invariant, invariant₁, invariant₂, invariant₃, invariant₄, invariant₅]
      intros ; simp [*] ; omega

    variant := fun b2 => (bval b2.mainlandPass) + (bval b2.islandPass)

    convergence := fun b2 => by
      intro Hinv ⟨Hgrd₁,_⟩
      simp [Machine.invariant, invariant₅, Hgrd₁] at Hinv
      simp [Hinv]

    simulation := fun b2 => by simp [Refinement.refine, refine]
  }


end Bridge2

end BridgeSpec
