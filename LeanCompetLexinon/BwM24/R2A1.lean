import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Choose.Sum

namespace BwM24R2A1

section Problem

def equation (x y : ℤ) : Prop := (x + 2) ^ 4 - x ^ 4 = y ^ 3

end Problem

-- ==============================

section Proof

lemma equation_iff_quadratic (a b : ℤ) :
  equation (a - 1) (b + 2 * a) ↔
  0 = 12 * b * a ^ 2 + (6 * b ^ 2 - 8) * a + b ^ 3 := by
  conv =>
    lhs
    unfold equation
    rw [sub_add, show b + 2 * a = 2 * a + b by rw [add_comm]]
    simp
    rw [add_pow, sub_pow, add_pow]
    unfold Finset.sum
    unfold Nat.choose
    simp
    rw [add_sub_add_comm, add_sub_add_comm, add_sub_add_comm]
    simp
    rw [← two_mul, ← two_mul]
    rw [show a ^ 3 * 4 = 4 * a ^ 3 by rw [mul_comm], ← mul_assoc]
    rw [show a * 4 = 4 * a by rw [mul_comm], ← mul_assoc]
    simp
    rw [show 8 * a ^ 3 = 2 ^ 3 * a ^ 3 by rfl, ← mul_pow, add_right_inj]
    conv =>
      rhs; left
      rw [mul_comm, ← mul_assoc, mul_pow, ← mul_assoc]
      simp
      rw [mul_assoc, show a ^ 2 * b = b * a ^ 2 by rw [mul_comm], ← mul_assoc]
    conv =>
      rhs; right; left
      rw [mul_comm, ← mul_assoc, ← mul_assoc]
      simp
      rw [mul_assoc, show a * b ^ 2 = b ^ 2 * a by rw [mul_comm], ← mul_assoc]
    rw [← add_assoc, show 8 * a = -((-8) * a) by simp, neg_eq_iff_add_eq_zero, add_comm]
    rw [add_assoc, show b ^ 3 + (-8) * a = (-8) * a + b ^ 3 by rw [add_comm]]
    rw [add_assoc]
    conv =>
      lhs; right
      rw [← add_assoc, ← Distrib.right_distrib, ← sub_eq_add_neg]
    rw [← add_assoc, Eq.comm]

lemma exists_quadratic_root_imp_discrim_nonneg {a b c : ℤ} (h_a_neq_zero : a ≠ 0) :
  (∃ x, 0 = a * x ^ 2 + b * x + c) → 0 ≤ b ^ 2 - 4 * (a * c) := by
  intro ⟨x, h⟩
  have h' : b ^ 2 - 4 * (a * c) = (2 * (a * x) + b) ^ 2:= by
    rw [add_sq, mul_pow, sub_eq_iff_eq_add, add_assoc]
    conv =>
      rhs; right
      rw [add_comm]
    rw [← add_assoc, ← mul_assoc, mul_assoc]
    simp
    rw [← Distrib.left_distrib, ← Distrib.left_distrib]
    simp
    rw [mul_pow, sq, mul_assoc, mul_assoc, ← Distrib.left_distrib, ← Distrib.left_distrib]
    rw [mul_eq_zero_iff_left h_a_neq_zero, show x * b = b * x by rw [mul_comm], Eq.comm]
    exact h
  calc 0
    _ ≤ (2 * (a * x) + b) ^ 2 := sq_nonneg _
    _ = _ := h'.symm

lemma simp_discrim (b : ℤ) : (6 * b ^ 2 - 8) ^ 2 - 4 * ((12 * b) * b ^ 3) =
  -(12 * b ^ 4) - 96 * b ^ 2 + 64 := by
  conv =>
    lhs
    conv =>
      right
      rw [mul_assoc, ← mul_assoc]
      conv =>
        right; left
        rw [← pow_one b]
      rw [← pow_add]
      simp
    conv =>
      left
      rw [sub_sq, mul_pow, ← pow_mul, mul_assoc]
      conv =>
        left; right; right
        rw [mul_comm, ← mul_assoc]
      rw [← mul_assoc]
      simp
    rw [sub_eq_add_neg, add_comm, ← add_assoc, add_sub_assoc', ← neg_mul, ← Distrib.right_distrib]
    simp

lemma b_eq_zero (b : ℤ) (h : 0 ≤ -(12 * b ^ 4) - 96 * b ^ 2 + 64) : b = 0 := by
  by_contra h_b_neq_zero
  have h_one_le_abs_b : 1 ≤ |b| := Int.one_le_abs h_b_neq_zero
  absurd (show ¬ (108 : ℤ) ≤ 64 by simp)
  conv at h =>
    rw [← neg_add_le_iff_le_add]
    simp
  calc
    (108 : ℤ) = 96 + 12 := by rfl
    _ ≤ 96 * b ^ 2 + 12 := by apply add_le_add_right; simp; exact h_one_le_abs_b
    _ ≤ 96 * b ^ 2 + 12 * b ^ 4 := by
      apply add_le_add_left; rw [show 4 = 2 * 2 by rfl, pow_mul]; simp; exact h_one_le_abs_b
    _ ≤ 64 := h

end Proof

-- ==============================

section Result

def solution : Set (ℤ × ℤ) := {(-1, 0)}

theorem proof : ∀ x y, equation x y ↔ (x, y) ∈ solution := by
  intros x y
  constructor
  · let a := x + 1
    let b := y - 2 * a
    rw [show x = a - 1 by unfold a; simp, show y = b + 2 * a by unfold b; simp]
    intro h
    rw [equation_iff_quadratic] at h
    have h_b_eq_zero : b = 0 := by
      by_contra h'
      absurd h'
      apply b_eq_zero
      rw [← simp_discrim b]
      refine exists_quadratic_root_imp_discrim_nonneg ?_ ⟨a, h⟩
      simp
      exact h'
    rw [h_b_eq_zero] at h
    simp at h
    rw [h, h_b_eq_zero]
    unfold solution
    simp
  · intro h
    unfold solution at h
    simp at h
    rw [h.left, h.right]
    unfold equation
    simp

end Result

end BwM24R2A1
