
--import LeanMachinesExamples.MQueue.Comparable

import Mathlib.Data.Finset.Dedup

namespace Sorted

instance: LawfulBEq Ordering where
  eq_of_beq := by
    intros a b
    intro H
    cases a <;> cases b <;>  simp_arith at *

  rfl := by
    intro a ; cases a <;> simp_arith

theorem OrdSplit [Ord α] (x y : α):
  compare x y = Ordering.gt ∨ compare x y = Ordering.lt ∨ compare x y = Ordering.eq :=
by
  cases (compare x y) <;> simp

@[local simp]
def isSorted [Ord α]: List α → Bool
  | [] => true
  | [_] => true
  | n₁::n₂::ns => match compare n₁ n₂ with
                  | Ordering.gt => false
                  | _ => isSorted (n₂::ns)

example: isSorted [4, 1, 2, 4, 3] = false := by  rfl
example: isSorted [1, 2, 3, 4, 4] = true := by  rfl

set_option linter.dupNamespace false

inductive Sorted [Ord α]: List α → Prop where
  | empty: Sorted []
  | single (x : α): Sorted [x]
  | more (x₁ x₂ : α) (xs : List α):
      compare x₁ x₂ = Ordering.lt ∨ compare x₁ x₂ = Ordering.eq
      → Sorted (x₂::xs)
      → Sorted (x₁::x₂::xs)

example: Sorted [1, 2, 3, 4, 4] :=
by
  repeat
    (constructor
     · --simp [compare, natCompare]
       simp_arith [compare]
     )
  constructor

example: ¬ Sorted [4, 1, 2, 4, 3] :=
by intro Hcontra
   cases Hcontra
   case more H₁ H₂ =>
     simp_arith [compare]at H₁

theorem Sorted_inv [Ord α] (x : α) (xs : List α):
  Sorted (x :: xs) → Sorted xs :=
by
  intros H
  cases H <;> (first | constructor | assumption)

theorem isSorted_inv [Ord α] (x : α) (xs : List α):
  isSorted (x :: xs) = true → isSorted xs = true:=
by
  intro H
  cases xs
  case nil => simp
  case cons y ys =>
    simp at H
    have Hcmp := OrdSplit x y
    cases Hcmp
    case inl Hgt => simp [Hgt] at H
    case inr Hcmp =>
      cases Hcmp <;> simp [*] at H <;> assumption

theorem Sorted_isSorted [Ord α] (xs : List α):
  Sorted xs → isSorted xs = true :=
by
  intro H
  induction H
  case empty => constructor
  case single => constructor
  case more x₁ x₂ xs' H₁ H₂ Hind =>
    simp
    split
    case h_1 Heq => rw [Heq] at H₁
                    cases H₁ <;> contradiction
    · assumption

theorem isSorted_Sorted [Ord α] (xs : List α):
  isSorted xs = true → Sorted xs :=
by
  intro H ; induction xs
  case nil => constructor
  case cons x xs Hind =>
    cases xs
    case nil => constructor
    case cons y ys =>
      constructor
      · simp at H
        have Hcmp: _ := OrdSplit x y
        cases Hcmp
        case a.inl Hcmp => rw [Hcmp] at H ; contradiction
        case a.inr Hcmp => assumption
      · apply Hind
        apply isSorted_inv (x:=x) (xs:=y::ys) ; assumption

def isPermutation [DecidableEq α] (xs ys : List α) : Prop :=
  xs.toFinset = ys.toFinset

theorem isPermutation_refl [DecidableEq α] (xs : List α):
  isPermutation xs xs :=
by
   simp [isPermutation]

theorem isPermutation_sym [DecidableEq α] (xs ys: List α):
  isPermutation xs ys → isPermutation ys xs :=
by
  simp [isPermutation]
  intro H
  simp [H]

theorem isPermutation_trans [DecidableEq α] (xs ys zs : List α):
  isPermutation xs ys → isPermutation ys zs
  → isPermutation xs zs :=
by
  simp [isPermutation]
  intros H₁ H₂
  simp [H₁, H₂]

theorem isPermutation_cons [DecidableEq α] (x : α) (xs ys : List α):
  isPermutation xs ys → isPermutation (n::xs) (n::ys) :=
by
  unfold isPermutation
  intro H
  refine List.toFinset.ext ?_
  intro x
  constructor
  · simp
    intro H₂
    cases H₂
    case _ Heq =>
      left ; assumption
    case _ Hin =>
      right
      have Hin' : x ∈ xs.toFinset := by exact List.mem_toFinset.mpr Hin
      rw [H] at Hin'
      exact List.mem_dedup.mp Hin'
  · simp
    intro H₂
    cases H₂
    case _ Heq =>
      left ; assumption
    case _ Hin =>
      right
      have Hin' : x ∈ ys.toFinset := by exact List.mem_toFinset.mpr Hin
      rw [←H] at Hin'
      exact List.mem_dedup.mp Hin'

theorem isPermutation_transpose [DecidableEq α] (x y : α) (xs ys : List α):
  isPermutation xs ys
  → isPermutation (x::y::xs) (y::x::ys) :=
by
  unfold isPermutation
  intro Heq
  refine List.toFinset.ext ?_
  intro a
  constructor
  case mp =>
    simp
    intro Hin
    cases Hin
    case inl Heq =>
      simp [Heq]
    case inr Hin =>
      cases Hin
      case inl Heq =>
        simp [Heq]
      case inr Hin =>
        right ; right
        have Hin' : a ∈ xs.toFinset := by exact List.mem_toFinset.mpr Hin
        rw [Heq] at Hin'
        exact List.mem_dedup.mp Hin'
  case mpr =>
    simp
    intro Hin
    cases Hin
    case inl Heq =>
      simp [Heq]
    case inr Hin =>
      cases Hin
      case inl Heq =>
        simp [Heq]
      case inr Hin =>
        right ; right
        have Hin' : a ∈ ys.toFinset := by exact List.mem_toFinset.mpr Hin
        rw [←Heq] at Hin'
        exact List.mem_dedup.mp Hin'

@[local simp]
def insertion [Ord α] (x : α) (xs : List α) : List α :=
  match xs with
  | [] => [x]
  | y::ys => if compare x y == Ordering.lt
             then x :: y :: ys
             else y :: insertion x ys

example: insertion 3 [1, 2, 4, 6] = [1, 2, 3, 4, 6] := by rfl
example: insertion 3 [4, 7, 9] = [3, 4, 7, 9] := by rfl
example: insertion 3 [3,4,6] = [3, 3, 4, 6] := by rfl

theorem insertion_perm [Ord α] [DecidableEq α] (x : α) (xs : List α):
  isPermutation (x::xs) (insertion x xs) :=
by
  induction xs
  case nil => simp [insertion, isPermutation]
  case cons y ys Hind =>
    simp [insertion] at *
    split
    case isTrue _ => apply isPermutation_refl

    case isFalse _ =>
      have H₁: isPermutation (y :: x :: ys) (y :: insertion x ys) := by
        apply isPermutation_cons <;> assumption

      have H₂: isPermutation (x :: y :: ys) (y :: x :: ys) := by
        apply isPermutation_transpose ; apply isPermutation_refl

      apply isPermutation_trans (ys:=y :: x :: ys) <;> assumption

theorem isSorted_cons [Ord α] (x y : α) (xs : List α):
  compare x y = Ordering.lt
  → isSorted (y::xs)
  → isSorted (x::y::xs) :=
by
  intro Hcmp
  simp [Hcmp]

theorem Sorted_cons [Ord α] (x y : α) (xs : List α):
  compare x y = Ordering.lt
  → Sorted (y::xs)
  → Sorted (x::y::xs) :=
by
  intros Hcmp Hsort
  refine isSorted_Sorted (x :: y :: xs) ?_
  refine isSorted_cons x y xs Hcmp ?_
  exact Sorted_isSorted (y :: xs) Hsort

theorem insertion_Sorted [Ord α] (x : α) (xs : List α):
  Sorted xs → Sorted (insertion x xs) :=
by
  intro Hsort
  induction Hsort
  case empty =>
    simp
    constructor
  case single x y =>
    simp
    split
    case isTrue Hlt =>
      constructor
      · left
        apply eq_of_beq
        simp [Hlt]
      · constructor
    case isFalse Hnlt =>
      constructor
      · have Hsplit := OrdSplit y x
        cases Hsplit
        case _ Hgt =>
          -- need symmetric cases for compare  (hence Comparable)
          sorry
        case _ Hngt =>
          assumption
      · constructor
  case more x₁ x₂ ys Hcmp Hsort Hind =>
    cases Hcmp
    case inl Hlt =>
      simp at *
      by_cases compare x x₁ = Ordering.lt
      case pos Hlt₁ =>
        simp [Hlt₁]
        have Htrans: compare x x₂ = Ordering.lt := by
          -- need transitivity
          sorry
        simp [Htrans] at Hind
        refine Sorted_cons x x₁ (x₂ :: ys) Hlt₁ ?_
        exact Sorted_cons x₁ x₂ ys Hlt Hsort
      case neg Hnlt₁ =>
        simp [Hnlt₁]
        by_cases compare x x₂ = Ordering.lt
        case pos Hlt₂ =>
          simp [Hlt₂]
          simp [Hlt₂] at Hind
          refine Sorted.more x₁ x (x₂ :: ys) ?_ Hind
          have Hneglt: ¬ (compare x x₁ = Ordering.lt) → (compare x₁ x = Ordering.lt ∨ compare x₁ x = Ordering.eq) := by
            -- need some form of completeness
            sorry
          simp [Hnlt₁] at Hneglt
          assumption
        case neg Hnlt₂ =>
          simp [Hnlt₂]
          simp [Hnlt₂] at Hind
          exact Sorted_cons x₁ x₂ (insertion x ys) Hlt Hind
    case inr Heq =>
      simp at *
      by_cases compare x x₂ = Ordering.lt
      case pos Hlt =>
        simp [Hlt]
        simp [Hlt] at Hind
        have Htrans: compare x x₁ = Ordering.lt := by
          -- need a kind of transitivity
          sorry
        simp [Htrans]
        refine Sorted_cons x x₁ (x₂ :: ys) Htrans ?_
        refine Sorted.more x₁ x₂ ys ?_ Hsort
        simp [Heq]
      case neg Hnlt =>
        simp [Hnlt]
        simp [Hnlt] at Hind
        have Hnlt': ¬ compare x x₁ = Ordering.lt := by
          -- need a kind of subtitution
          sorry
        simp [Hnlt']
        refine Sorted.more x₁ x₂ (insertion x ys) ?_ Hind
        right
        assumption


theorem insertion_sorted [Ord α] (x : α) (xs : List α):
  isSorted xs → isSorted (insertion x xs) :=
by
  intro Hsort
  refine Sorted_isSorted (insertion x xs) ?_
  refine insertion_Sorted x xs ?_
  exact isSorted_Sorted xs Hsort


end Sorted
