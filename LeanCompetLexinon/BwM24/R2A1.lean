import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Sum

section Problem

def equation (x y : Int) : Prop := (x + 2) ^ 4 - x ^ 4 = y ^ 3

end Problem

-- ==============================

section Proof

theorem aux : ∀ a b c d : Int, (a + b) - (c + d) = (a - c) + (b - d) := by
  intro a b c d
  conv =>
    lhs
    rw [Int.add_sub_assoc, Int.sub_eq_add_neg, Int.neg_add]
    conv =>
      right
      conv =>
        right
        rw [Int.add_comm]
      rw [← Int.add_assoc]
    rw [← Int.add_assoc, Int.add_comm, ← Int.add_assoc]
    conv =>
      left
      rw [Int.add_comm, ← Int.sub_eq_add_neg]
    rw [← Int.sub_eq_add_neg]

end Proof

-- ==============================

section Result

def solution : Set (Int × Int) := {(-1, 0)}

theorem proof : ∀ (x y : Int), equation x y ↔ (x, y) ∈ solution := by
  intros x y
  constructor
  · let a := x + 1
    let b := y - 2 * a
    rw [← show a - 1 = x from x.add_sub_cancel 1, ← show b + 2 * a = y from y.sub_add_cancel (2 * a)]
    unfold equation
    unfold solution
    intro h
    conv at h =>
      lhs
      left
      left
      rw [Int.sub_eq_add_neg, Int.add_assoc]
      simp
    rw [add_pow, sub_pow, add_pow] at h
    unfold Finset.sum at h
    unfold Nat.choose at h
    simp at h
    conv at h =>
      lhs
      rw [aux, Int.sub_neg, ← Int.two_mul, Int.mul_comm, Int.mul_assoc]
      right
      rw [aux, Int.sub_eq_zero.mpr rfl, Int.zero_add]
      rw [aux, Int.sub_neg, ← Int.two_mul, Int.mul_comm, Int.mul_assoc]
    simp at h
    conv at h =>
      rhs
      right
      conv =>
        left
        rw [Int.mul_assoc]
        conv => right; left; rw [Int.mul_comm]
        rw [Int.mul_assoc, ← Int.mul_assoc]
        simp
      right
      conv =>
        left
        conv => left; right; rw [Int.mul_comm, mul_pow]
        rw [← Int.mul_assoc, Int.mul_assoc]
        simp
      right
      conv =>
        rw [Int.mul_comm, mul_pow]
        simp
    sorry
  · intro h
    unfold solution at h
    simp at h
    rw [h.left, h.right]
    rfl

end Result
