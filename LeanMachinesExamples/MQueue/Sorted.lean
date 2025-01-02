
import LeanMachinesExamples.MQueue.Comparable

namespace Sorted


@[local simp]
def isSorted [Comparable α]: List α → Bool
  | [] => true
  | [_] => true
  | n₁::n₂::ns => match compare n₁ n₂ with
                  | Ordering.gt => false
                  | _ => isSorted (n₂::ns)

example: isSorted [4, 1, 2, 4, 3] = false := by  rfl
example: isSorted [1, 2, 3, 4, 4] = true := by  rfl

inductive Sorted [Comparable α]: List α → Prop where
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
     · simp [compare, natCompare]
     )
  constructor

example: ¬ Sorted [4, 1, 2, 4, 3] :=
by intro Hcontra
   cases Hcontra
   case more H₁ H₂ =>
     simp_arith [compare] at H₁

theorem Sorted_inv [Comparable α] (x : α) (xs : List α):
  Sorted (x :: xs) → Sorted xs :=
by
  intros H
  cases H <;> (first | constructor | assumption)

theorem isSorted_inv [Comparable α] (x : α) (xs : List α):
  isSorted (x :: xs) = true → isSorted xs = true:=
by
  intro H
  cases xs
  case nil => simp
  case cons y ys =>
    simp at H
    have Hcmp := ComparableSplit x y
    cases Hcmp
    case inl Hgt => simp [Hgt] at H
    case inr Hcmp =>
      cases Hcmp <;> simp [*] at H <;> assumption
  done

theorem Sorted_isSorted [Comparable α] (xs : List α):
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
  done

theorem isSorted_Sorted [Comparable α] (xs : List α):
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
        have Hcmp: _ := ComparableSplit x y
        cases Hcmp
        case a.inl Hcmp => rw [Hcmp] at H ; contradiction
        case a.inr Hcmp => assumption
      · apply Hind
        apply isSorted_inv (x:=x) (xs:=y::ys) ; assumption
  done

@[local simp]
def nbOcc [Comparable α] (x : α) (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => match compare y x with
               | Ordering.eq => Nat.succ (nbOcc x ys)
               | _ => nbOcc x ys

example: nbOcc 3 [3, 7, 3, 4] = 2 := by rfl
example: nbOcc 6 [3, 7, 3, 4] = 0 := by rfl

theorem nbOcc_zero_cons [Comparable α] (x : α):
  nbOcc x (y :: ys) = 0
  -> x ≠ y :=
by
  simp
  split
  · simp
  case h_2 Hneq =>
    intros Hnb Heq
    rw [Heq] at Hneq
    rw [Comparable.compare_refl] at Hneq
    contradiction

theorem nbOcc_zero_cons_rest [Comparable α] (x : α):
  nbOcc x (y :: ys) = 0
  -> nbOcc x ys = 0 :=
by
  intro Hnb
  have Hneq: x ≠ y := by apply nbOcc_zero_cons ; assumption
  simp [nbOcc] at Hnb
  have Hneq': compare y x ≠ Ordering.eq := by
    have Hneq': compare x y ≠ Ordering.eq := by
      apply Comparable_neq_neq_complete
      assumption
    intro Heq
    have Hcontra: compare x y = Ordering.eq := by
      apply Comparable.compare_eq_sym ; assumption
    contradiction
  simp [Hneq'] at Hnb
  assumption

theorem nbOcc_Zero_notMem [Comparable α] (x : α) (xs : List α):
  ¬ List.Mem x xs
  → nbOcc x xs = 0 :=
by
  intro Hmem
  induction xs
  case nil => simp
  case cons x y ys Hind =>
    simp_arith
    split
    case h_1 Heq =>
      simp
      apply Hmem
      have Hxy: y = x := by
        apply Comparable.compare_eq_eq
        assumption
      rw [Hxy]
      constructor
    case h_2 Hneq =>
      apply Hind
      intro Hmem'
      apply Hmem
      constructor
      assumption
  done

theorem nbOcc_notMem_Zero [Comparable α] (x : α) (xs : List α):
  nbOcc x xs = 0
  →  ¬ List.Mem x xs :=
by
  intro Hnb
  induction xs
  case nil =>
    intro Hcontra
    cases Hcontra
  case cons y xs Hind =>
    intro Hcontra
    cases Hcontra
    case head =>
      simp [nbOcc, Comparable.compare_refl] at Hnb
    case tail H1 =>
      apply Hind
      · apply nbOcc_zero_cons_rest ; assumption
      · assumption


theorem nbOcc_Mem_ne_Zero [Comparable α] (x : α) (xs : List α):
  nbOcc x xs ≠ 0
  → List.Mem x xs :=
by
  induction xs
  case nil => simp
  case cons y xs Hind =>
    intro H1
    by_cases x = y
    case pos Heq =>
      rw [←Heq]
      constructor
    case neg Hneq =>
      constructor
      case a =>
        apply Hind
        simp at H1
        have Hcmp := ComparableSplit y x
        cases Hcmp
        case inl Hgt =>
          simp [Hgt] at H1
          simp [H1]
        case inr Hcmp =>
          cases Hcmp
          case inl Hlt =>
            simp [Hlt] at H1
            simp [H1]
          case inr Heq =>
            have Hcontra: y = x := by
              apply Comparable.compare_eq_eq ; assumption
            rw [Hcontra] at Hneq
            contradiction
  done

theorem nbOcc_ne_zero [Comparable α] (x : α) (xs : List α):
  List.Mem x xs
  → nbOcc x xs ≠ 0 :=
by
  intro Hmem
  intro Hnb
  have Hcontra: ¬ List.Mem x xs := by
    apply nbOcc_notMem_Zero ; assumption
  contradiction

theorem nbOcc_last_first [Comparable α] (x : α) (xs : List α):
  nbOcc x (x :: xs) = 1
  → nbOcc x xs = 0 :=
by
  simp [Comparable.compare_refl]

def nbOcc_perm [Comparable α] (x y z : α) (xs : List α):
  nbOcc x (y :: z :: xs) = nbOcc x (z :: y :: xs) :=
by
  cases xs
  case nil =>
    simp
    by_cases compare y x = Ordering.eq
    case pos Heq₁ =>
      simp [Heq₁]
      by_cases compare z x = Ordering.eq
      case pos Heq₂ =>
        simp [Heq₂]
      case neg Hneq₂ =>
        simp [Hneq₂]
    case neg Hneq₁ =>
      simp [Hneq₁]
  case cons x' xs =>
    simp
    by_cases compare y x = Ordering.eq
    case pos Heq₁ =>
      simp [Heq₁]
      by_cases compare z x = Ordering.eq
      case pos Heq₂ =>
        simp [Heq₂]
      case neg Hneq₂ =>
        simp [Hneq₂]
    case neg Hneq₁ =>
      simp [Hneq₁]
  done

def permutation [Comparable α] (xs ys : List α) : Prop :=
  ∀ x : α, nbOcc x xs = nbOcc x ys


end Sorted
