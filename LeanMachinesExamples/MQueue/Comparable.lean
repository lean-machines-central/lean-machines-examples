class Comparable (α : Type u) extends (Ord α) where
  --compare : α → α → Ordering
  compare_refl: ∀ x : α, compare x x = Ordering.eq
  compare_gt_sym:
    ∀ x y : α, compare x y = Ordering.gt
               → compare y x = Ordering.lt
  compare_lt_sym:
    ∀ x y : α, compare x y = Ordering.lt
               → compare y x = Ordering.gt

  compare_eq_sym:
    ∀ x y : α, compare x y = Ordering.eq → compare y x = Ordering.eq

  compare_eq_eq:
    ∀ x y : α, compare x y = Ordering.eq → x = y

open Comparable

theorem Comparable_neq_neq [Comparable α] (x y : α):
  compare x y ≠ Ordering.eq
  → x ≠ y :=
by
  intros Hcmp Heq
  rw [Heq] at Hcmp
  have Hrefl: compare y y = Ordering.eq := compare_refl y
  contradiction

theorem Comparable_neq_neq_complete [Comparable α] (x y : α):
  x ≠ y → compare x y ≠ Ordering.eq :=
by
  intros Hneq Hcmp
  apply Hneq
  apply compare_eq_eq
  assumption


theorem Comparable_eq_eq_complete [Comparable α] (x y : α):
  x = y → compare x y = Ordering.eq :=
by
  intro Heq
  rw [Heq]
  apply compare_refl

theorem ComparableSplit [Comparable α] (x y : α):
  compare x y = Ordering.gt ∨ compare x y = Ordering.lt ∨ compare x y = Ordering.eq :=
by
  cases (compare x y) <;> simp

theorem ComparableNotLtGt_Eq [Comparable α] (x y : α):
  compare x y ≠ Ordering.gt
  → compare x y ≠ Ordering.lt
  → compare x y = Ordering.eq :=
by
  intros H1 H2
  have Hcmp: _ := ComparableSplit x y
  cases Hcmp
  · contradiction
  case inr Hcmp =>
    cases Hcmp
    · contradiction
    · assumption

def ordThen (ord₁ ord₂ : Ordering) : Ordering :=
  match ord₁ with
  | Ordering.lt => Ordering.lt
  | Ordering.gt => Ordering.gt
  | _ => ord₂

-- Remark:  Nat.blt and Nat.beq are supposed to be fast
def natCompare (m n : Nat) :=
  if Nat.blt m n then Ordering.lt
  else if Nat.beq m n  then Ordering.eq
  else Ordering.gt

def natCompare_correct (m n : Nat) :
  natCompare m n = compare m n :=
by
  simp [natCompare, compare, compareOfLessAndEq]

theorem ifTrue (p : Prop) [Decidable p] (e₁ e₂ : α):
  p → (if p then e₁ else e₂) = e₁ :=
by
  intro Hp
  split <;> rfl
  done

theorem ifFalse (p : Prop) [Decidable p] (e₁ e₂ : α):
  ¬p → (if p then e₁ else e₂) = e₂ :=
by
  intro Hnp
  split
  · contradiction
  · rfl
  done

theorem Nat_lt_of_not_lt_not_eq (m n : Nat):
  ¬m < n → m ≠ n → n < m :=
by
  intros H₁ H₂
  rw [Nat.not_lt_eq] at H₁
  apply Nat.lt_of_le_of_ne
  · assumption
  · intro Heq
    rw [Heq] at H₂
    contradiction
  done

theorem natCompareGt (m n : Nat):
  natCompare m n = Ordering.gt
  → natCompare n m = Ordering.lt :=
by
  simp [natCompare]
  intro Hmn
  split
  case isTrue Hlt => simp [Hlt] at Hmn
  case isFalse Hgt =>
    intro Hle
    have Hlt : m < n := by exact Nat.lt_of_le_of_ne Hle fun a => Hgt (id (Eq.symm a))
    simp [Hlt] at Hmn
  done

theorem natCompare_lt (m n : Nat):
  natCompare m n = Ordering.lt → m < n :=
by
  simp [natCompare]
  intro Hif
  by_cases (m < n)
  case pos Hinf => assumption
  case neg Hninf =>
    have Hle: n ≤ m := by exact Nat.le_of_not_lt Hninf
    simp [Hle] at Hif
    by_cases m = n
    case pos Hpos => simp [Hpos] at Hif
    case neg Hneg => simp [Hneg] at Hif
  done

theorem natCompare_gt (m n : Nat):
  natCompare m n = Ordering.gt → n < m :=
by
  intro H₁
  have H₂: natCompare n m = Ordering.lt := by
    apply natCompareGt
    assumption
  apply natCompare_lt
  · assumption
  done

theorem natCompare_eq (m n : Nat):
  natCompare m n = Ordering.eq → m = n :=
by
  simp [natCompare]
  split
  case isTrue H₁ => intro Hcontra ; contradiction
  case isFalse H₁ =>
    split
    case isTrue H₂ => intros ; assumption
    case isFalse H₂ => intros ; contradiction
  done

theorem lt_natCompare (m n : Nat):
  m < n → natCompare m n = Ordering.lt :=
by
  intro H₁
  simp [natCompare]
  omega

theorem Nat_ne_sym (m n : Nat):
  m ≠ n → n ≠ m :=
by
  intro Hneq
  intro Heq
  rw [Heq] at Hneq
  contradiction
  done

theorem gt_natCompare (m n : Nat):
  m > n → natCompare m n = Ordering.gt :=
by
  simp [GT.gt]
  intro H₁
  simp [natCompare]
  split
  case isTrue H₂ =>
    have Hrefl: n < n := by
      apply Nat.lt_trans (m:=m) <;> assumption
    have Hcontra: ¬ n < n := Nat.lt_irrefl n
    contradiction
  case isFalse H₂ =>
    clear H₂ -- useless
    have H₂: m ≠ n := by
      apply Nat_ne_sym
      · apply Nat.ne_of_lt
        · assumption
    rw [ifFalse]
    · simp [H₂]
  done

theorem eq_natCompare (m n : Nat):
  m = n → natCompare m n = Ordering.eq :=
by
  intro Heq <;> simp [natCompare, Heq]

theorem natCompareRefl (n : Nat):
  natCompare n n = Ordering.eq :=
by
  simp [natCompare]

theorem natCompareTrans (m n p : Nat):
  natCompare m n = Ordering.eq
  → natCompare n p = Ordering.eq
  → natCompare m p = Ordering.eq :=
by
  intros H₁ H₂
  apply eq_natCompare
  have H₁': m = n := by apply natCompare_eq ; assumption
  have H₂': n = p := by apply natCompare_eq ; assumption
  simp [H₁', H₂']
  done

theorem  natCompare_gt_sym (x y : Nat):
    natCompare x y = Ordering.gt
    → natCompare y x = Ordering.lt :=
by
  intro H
  have H': y < x := natCompare_gt x y H
  apply lt_natCompare ; assumption

theorem  natCompare_lt_sym (x y : Nat):
    natCompare x y = Ordering.lt
    → natCompare y x = Ordering.gt :=
by
  intro H
  have H': x < y := natCompare_lt x y H
  apply gt_natCompare ; assumption

theorem natCompare_eq_sym (x y : Nat):
  natCompare x y = Ordering.eq → natCompare y x = Ordering.eq :=
by
  intro H
  have H': x = y := by apply natCompare_eq ; assumption
  apply eq_natCompare ; simp [H']

theorem natCompare_eq_eq (x y : Nat):
  natCompare x y = Ordering.eq
  → x = y :=
by
  simp [natCompare]
  split
  · simp
  · split
    · intros ; assumption
    · simp
  done

instance: Comparable Nat where
  compare := natCompare
  compare_refl := natCompareRefl
  compare_gt_sym := natCompare_gt_sym
  compare_lt_sym := natCompare_lt_sym
  compare_eq_sym := natCompare_eq_sym
  compare_eq_eq := natCompare_eq_eq

theorem natCompareSplit (x y : Nat):
  natCompare x y = Ordering.gt ∨ natCompare x y = Ordering.lt ∨ natCompare x y = Ordering.eq :=
by
  apply ComparableSplit x y


def cmp_List [Comparable α] (xs ys: List α): Ordering :=
  match xs with
  | [] => match ys with
          | [] => Ordering.eq
          | _ => Ordering.lt
  | x::xs' => match ys with
              | [] => Ordering.gt
              | (y::ys') => match compare x y with
                            | Ordering.lt => Ordering.lt
                            | Ordering.gt => Ordering.gt
                            | Ordering.eq => cmp_List xs' ys'

theorem cmp_List_refl [Comparable α] (xs : List α):
  cmp_List xs xs = Ordering.eq :=
by
  induction xs
  case nil => simp [cmp_List]
  case cons x xs Hind =>
    simp [cmp_List, compare_refl, Hind]

theorem List_ind_par (P : List α → List α → Prop):
 P [] []
 → (∀ (x : α) (xs : List α), P (x::xs) [])
 → (∀ (y : α) (ys : List α), P [] (y::ys))
 → (∀ xs ys : List α, P xs ys → ∀ x y : α, P (x::xs) (y::ys))
 → ∀ xs ys : List α, P xs ys :=
by
  intros Hnil Hnilᵣ Hnilₗ Hind xs
  induction xs
  case nil => intro ys
              cases ys
              case nil => assumption
              case cons y ys => apply Hnilₗ
  case cons x xs Hind' =>
    intro ys
    cases ys
    case nil => apply Hnilᵣ
    case cons y ys =>
      apply Hind
      · apply Hind'
  done

theorem cmp_List_gt_sym_nil [Comparable α]:
  cmp_List ([]:List α) [] = Ordering.gt
  → cmp_List ([]:List α) [] = Ordering.lt :=
by
  simp [cmp_List]

theorem cmp_List_gt_sym_nil_left [Comparable α] (y : α) (ys : List α):
  cmp_List [] (y::ys) = Ordering.gt
  → cmp_List (y::ys) [] = Ordering.lt :=
by
  simp [cmp_List]

theorem cmp_List_gt_sym_nil_right [Comparable α] (x : α) (xs : List α):
  cmp_List (x::xs) [] = Ordering.gt
  → cmp_List [] (x::xs) = Ordering.lt :=
by
  simp [cmp_List]

-- (∀ xs ys : List α, P xs ys → ∀ x y : α, P (x::xs) (y::ys))
theorem cmp_List_gt_sym_ind [Comparable α] (xs ys : List α):
  (cmp_List xs ys = Ordering.gt → cmp_List ys xs = Ordering.lt)
  → ∀ x y : α, (cmp_List (x::xs) (y::ys) = Ordering.gt
                → cmp_List (y::ys) (x::xs) = Ordering.lt) :=
by
  intros H1 x y H2
  simp [cmp_List] at H2
  simp [cmp_List]
  cases (ComparableSplit x y)
  case inl Hgt => simp [compare_gt_sym, Hgt]
  case inr Hcmp =>
    cases Hcmp
    case inl Hlt => rw [Hlt] at H2
                    simp at H2
    case inr Heq => rw [Heq] at H2
                    simp at H2
                    simp [compare_eq_sym, Heq]
                    apply H1
                    assumption
  done

theorem cmp_List_gt_sym [Hcomp: Comparable α]:
  ∀ xs ys : List α,
  (cmp_List xs ys = Ordering.gt
  → cmp_List ys xs = Ordering.lt) :=
by
  apply (@List_ind_par α)
  · apply @cmp_List_gt_sym_nil α Hcomp
  · apply @cmp_List_gt_sym_nil_right α Hcomp
  · apply @cmp_List_gt_sym_nil_left α Hcomp
  · apply @cmp_List_gt_sym_ind α Hcomp

theorem cmp_List_lt_sym_nil [Comparable α]:
  cmp_List ([]:List α) [] = Ordering.lt
  → cmp_List ([]:List α) [] = Ordering.gt :=
by
  simp [cmp_List]

theorem cmp_List_lt_sym_nil_left [Comparable α] (y : α) (ys : List α):
  cmp_List [] (y::ys) = Ordering.lt
  → cmp_List (y::ys) [] = Ordering.gt :=
by
  simp [cmp_List]

theorem cmp_List_lt_sym_nil_right [Comparable α] (x : α) (xs : List α):
  cmp_List (x::xs) [] = Ordering.lt
  → cmp_List [] (x::xs) = Ordering.gt :=
by
  simp [cmp_List]

theorem cmp_List_lt_sym_ind [Comparable α] (xs ys : List α):
  (cmp_List xs ys = Ordering.lt → cmp_List ys xs = Ordering.gt)
  → ∀ x y : α, (cmp_List (x::xs) (y::ys) = Ordering.lt
                → cmp_List (y::ys) (x::xs) = Ordering.gt) :=
by
  intros H1 x y H2
  simp [cmp_List] at H2
  simp [cmp_List]
  cases (ComparableSplit x y)
  case inl Hgt => rw [Hgt] at H2
                  simp at H2
  case inr Hcmp =>
    cases Hcmp
    case inl Hlt => simp [compare_lt_sym, Hlt]
    case inr Heq => rw [Heq] at H2
                    simp at H2
                    simp [compare_eq_sym, Heq]
                    apply H1
                    assumption
  done

theorem cmp_List_lt_sym [Hcomp: Comparable α]:
  ∀ xs ys : List α,
  (cmp_List xs ys = Ordering.lt
  → cmp_List ys xs = Ordering.gt) :=
by
  apply (@List_ind_par α)
  · apply @cmp_List_lt_sym_nil α Hcomp
  · apply @cmp_List_lt_sym_nil_right α Hcomp
  · apply @cmp_List_lt_sym_nil_left α Hcomp
  · apply @cmp_List_lt_sym_ind α Hcomp

theorem cmp_List_eq_sym_nil [Comparable α]:
  cmp_List ([]:List α) [] = Ordering.eq
  → cmp_List ([]:List α) [] = Ordering.eq :=
by
  simp [cmp_List]

theorem cmp_List_eq_sym_nil_left [Comparable α] (y : α) (ys : List α):
  cmp_List [] (y::ys) = Ordering.eq
  → cmp_List (y::ys) [] = Ordering.eq :=
by
  simp [cmp_List]

theorem cmp_List_eq_sym_nil_right [Comparable α] (x : α) (xs : List α):
  cmp_List (x::xs) [] = Ordering.eq
  → cmp_List [] (x::xs) = Ordering.eq :=
by
  simp [cmp_List]

theorem cmp_List_eq_sym_ind [Comparable α] (xs ys : List α):
  (cmp_List xs ys = Ordering.eq → cmp_List ys xs = Ordering.eq)
  → ∀ x y : α, (cmp_List (x::xs) (y::ys) = Ordering.eq
                → cmp_List (y::ys) (x::xs) = Ordering.eq) :=
by
  intros H1 x y H2
  simp [cmp_List] at H2
  simp [cmp_List]
  cases (ComparableSplit x y)
  case inl Hgt => rw [Hgt] at H2
                  simp at H2
  case inr Hcmp =>
    cases Hcmp
    case inl Hlt => rw [Hlt] at H2
                    simp at H2
    case inr Heq => rw [Heq] at H2
                    simp at H2
                    simp [compare_eq_sym, Heq]
                    apply H1
                    assumption
  done

theorem cmp_List_eq_sym [Hcomp: Comparable α]:
  ∀ xs ys : List α,
  (cmp_List xs ys = Ordering.eq
  → cmp_List ys xs = Ordering.eq) :=
by
  apply (@List_ind_par α)
  · apply @cmp_List_eq_sym_nil α Hcomp
  · apply @cmp_List_eq_sym_nil_right α Hcomp
  · apply @cmp_List_eq_sym_nil_left α Hcomp
  · apply @cmp_List_eq_sym_ind α Hcomp

theorem cmp_List_eq_eq [Comparable α]:
  ∀ xs ys : List α,
  cmp_List xs ys = Ordering.eq
  → xs = ys :=
by
  intro xs
  induction xs
  case nil =>
    intro ys
    simp [cmp_List]
    cases ys <;> simp
  case cons x xs Hind =>
    intros ys
    simp [cmp_List]
    cases ys
    case nil =>
      simp
    case cons y ys =>
      simp
      split
      · intro Hfalse ; contradiction
      · intro Hfalse ; contradiction
      · intro Heq
        apply And.intro
        · apply compare_eq_eq
          assumption
        · apply Hind
          assumption
  done


instance [Comparable α]: Comparable (List α) where
  compare := cmp_List
  compare_refl := cmp_List_refl
  compare_gt_sym := cmp_List_gt_sym
  compare_lt_sym := cmp_List_lt_sym
  compare_eq_sym := cmp_List_eq_sym
  compare_eq_eq := cmp_List_eq_eq

def cmp_Char (c₁ c₂ : Char) :=
  --natCompare c₁.toNat c₂.toNat
  if c₁ < c₂ then Ordering.lt
  else if c₁ > c₂ then Ordering.gt
  else Ordering.eq

theorem cmp_Char_refl (x : Char):
  cmp_Char x x = Ordering.eq :=
by
  simp [cmp_Char]

theorem Nat_eq_of_le_ge (m n : Nat):
  m ≤ n → n ≤ m → m = n :=
by
  intros H1 H2
  have H3: _ := Nat.eq_or_lt_of_le H1
  cases H3
  case inl Heq => assumption
  case inr Hinf =>
    have H4: n > m := by simp [Hinf]
    have H5: _ := Nat.not_le_of_gt H4
    contradiction
  done

theorem cmp_Char_gt_sym (x y : Char):
  cmp_Char x y = Ordering.gt → cmp_Char y x = Ordering.lt :=
by
  simp [cmp_Char]
  intro H
  split
  case isTrue Hlt =>
    simp [Hlt] at H
  case isFalse Hnlt =>
    simp [Hnlt] at H
    intro Hle
    by_cases x = y
    case pos Hpos =>
      simp [Hpos] at H
    case neg Hneg =>
      simp [LT.lt, LE.le] at *
      simp [Char.le, Char.lt] at *
      have Hnegv: x.val ≠ y.val := by
        exact Char.val_ne_of_ne Hneg
      have Heq: x.val = y.val := by exact UInt32.le_antisymm Hle Hnlt
      contradiction
  done

theorem cmp_Char_lt_sym (x y : Char):
  cmp_Char x y = Ordering.lt → cmp_Char y x = Ordering.gt :=
by
  simp [cmp_Char]
  intro H
  split
  case isTrue Hlt =>
    simp [Hlt] at H
    unfold LT.lt at *
    simp [Char.instLT] at *
    simp [Char.lt] at *
    unfold LT.lt at *
    simp [instLTUInt32] at *
    unfold LT.lt at *
    simp [instLTBitVec] at *
    have Hcontra: ¬ (x.val.toBitVec.toNat < y.val.toBitVec.toNat) := by
      exact Nat.not_lt_of_gt Hlt
    contradiction
  case isFalse Hnlt =>
    simp [Hnlt] at H
    split
    case isTrue Hgt => rfl
    case isFalse Hngt =>
      simp [Hngt] at H
  done

theorem cmp_Char_eq_sym (x y : Char):
  cmp_Char x y = Ordering.eq → cmp_Char y x = Ordering.eq :=
by
  simp [cmp_Char]
  intro H
  split
  case isTrue Hlt =>
    simp [Hlt] at H
    split at H
    case isTrue Hlt =>
      assumption
    case isFalse Hcontra =>
      contradiction
  case isFalse Hnlt =>
    split at H
    case isTrue _ => contradiction
    case isFalse Hngt =>
      split
      · contradiction
      · rfl
  done

-- Taken from mathlib
--theorem Char.ofNat_toNat {c : Char} (h : isValidCharNat c.toNat) : Char.ofNat c.toNat = c := by
--  rw [Char.ofNat, dif_pos h]
--  rfl

theorem cmp_Char_eq_eq (x y : Char):
  cmp_Char x y = Ordering.eq → x = y :=
by
  simp [cmp_Char]
  split
  · simp
  case isFalse Hnlt =>
    split
    · simp
    case isFalse Hngt =>
      intro Htrue ; clear Htrue
      apply Char.eq_of_val_eq
      unfold LT.lt at *
      simp [Char.instLT] at *
      simp [Char.lt] at *
      exact UInt32.le_antisymm Hngt Hnlt
  done

instance: Comparable Char where
  compare := cmp_Char
  compare_refl := cmp_Char_refl
  compare_gt_sym := cmp_Char_gt_sym
  compare_lt_sym := cmp_Char_lt_sym
  compare_eq_sym := cmp_Char_eq_sym
  compare_eq_eq := cmp_Char_eq_eq

theorem String_eq_ext (s₁ s₂ : String):
  s₁.data = s₂.data
  → s₁ = s₂ :=
by
  intro h
  show ⟨s₁.data⟩ = (⟨s₂.data⟩ : String)
  simp [h]

def cmp_String (s₁ s₂ : String) :=
  cmp_List s₁.data s₂.data

theorem cmp_refl_String (x : String):
  cmp_String x x = Ordering.eq :=
by
  simp [cmp_String]
  apply cmp_List_refl

theorem cmp_gt_sym_String (x y : String):
  cmp_String x y = Ordering.gt → cmp_String y x = Ordering.lt :=
by
  simp [cmp_String]
  apply cmp_List_gt_sym

theorem cmp_lt_sym_String (x y : String):
  cmp_String x y = Ordering.lt → cmp_String y x = Ordering.gt :=
by
  simp [cmp_String]
  apply cmp_List_lt_sym

theorem cmp_eq_sym_String (x y : String):
  cmp_String x y = Ordering.eq → cmp_String y x = Ordering.eq :=
by
  simp [cmp_String]
  apply cmp_List_eq_sym

theorem cmp_eq_eq_String (x y : String):
  cmp_String x y = Ordering.eq → x = y :=
by
  simp [cmp_String]
  intro H
  apply String_eq_ext
  apply cmp_List_eq_eq
  assumption

instance: Comparable String where
  compare := cmp_String
  compare_refl := cmp_refl_String
  compare_gt_sym := cmp_gt_sym_String
  compare_lt_sym := cmp_lt_sym_String
  compare_eq_sym := cmp_eq_sym_String
  compare_eq_eq := cmp_eq_eq_String


/- Some simple lemmas about Ordering -/

theorem Ordering_eq_of_beq {o₁ o₂ : Ordering} (Heq: o₁ == o₂):
  o₁ = o₂ :=
by
  cases o₁ <;> cases o₂ <;> (first | rfl | contradiction)

theorem Ordering_rfl {o : Ordering}:
  (o == o) = true :=
by
  cases o <;> rfl

instance : LawfulBEq Ordering where
  eq_of_beq := Ordering_eq_of_beq
  rfl := Ordering_rfl
