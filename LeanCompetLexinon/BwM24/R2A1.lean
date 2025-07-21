/-
(c) Lexinon 2025
-/
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Choose.Sum

/-!
# BwM24 R2 A1

The contestants are asked to determine all integer solutions `(x, y)` of the equation
`(x + 2) ^ 4 - x ^ 4 = y ^ 3`.

It will be shown that `(-1, 0)` is the only solution.
-/

namespace BwM24R2A1

section Problem

/-! ## Definitions for setting up the problem -/

/-- The equation to be fulfilled by `(x, y)` as a `Prop`. -/
def equation (x y : ℤ) : Prop := (x + 2) ^ 4 - x ^ 4 = y ^ 3

end Problem

-- ==============================

section Proof

/-! ## Lemmas and definitions for the proof -/

lemma quadratic_of_equation {a b : ℤ} (h : equation (a - 1) (b + 2 * a)) :
    0 = 12 * b * a ^ 2 + (6 * b ^ 2 - 8) * a + b ^ 3 := by
  unfold equation at h
  rw [← zero_add ((b + 2 * a) ^ 3), ← sub_eq_iff_eq_add, ← neg_eq_zero] at h
  rw [← h]
  ring

lemma exists_quadratic_root_imp_discrim_nonneg {a b c : ℤ} :
    (∃ x, 0 = a * x ^ 2 + b * x + c) → 0 ≤ b ^ 2 - 4 * (a * c) := by
  intro ⟨x, h⟩
  have h'' : 4 * a * (a * x ^ 2 + b * x + c) = (2 * a * x + b) ^ 2 - (b ^ 2 - 4 * (a * c)) := by
    ring
  rw [← h] at h''
  simp at h''
  rw [eq_comm, sub_eq_zero] at h''
  rw [← h'']
  apply sq_nonneg

lemma simp_discrim (b : ℤ) : (6 * b ^ 2 - 8) ^ 2 - 4 * ((12 * b) * b ^ 3) =
    -(12 * b ^ 4) - 96 * b ^ 2 + 64 := by
  ring

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

/-! ## The solution and the proof of its correctness -/

/-- The set of all solutions of `equation`. -/
def solution : Set (ℤ × ℤ) := {(-1, 0)}

/-- Proof that the above `solution` is correct. -/
theorem proof : ∀ x y, equation x y ↔ (x, y) ∈ solution := by
  intros x y
  constructor
  · let a := x + 1
    let b := y - 2 * a
    rw [show x = a - 1 by unfold a; simp, show y = b + 2 * a by unfold b; simp]
    intro h
    have h := quadratic_of_equation h
    have h_b_eq_zero : b = 0 := by
      by_contra h'
      absurd h'
      apply b_eq_zero
      rw [← simp_discrim b]
      exact exists_quadratic_root_imp_discrim_nonneg ⟨a, h⟩
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
