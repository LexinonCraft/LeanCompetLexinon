/-
Copyright (c) Lexinon. All rights reserved.
Licensed under the MIT license. See LICENSE file in the project root for details.
-/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Finite.Defs
import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.Multiplicity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Factorization.Induction

/-!
# Bwm25 R1 A2

For each integer $n\geq2$ consider the last non-zero digit of $n!$. The sequence of these digits starts
with $2,6,4,2,2,\dots$. The contestants are asked to determine the digits that appear in this sequence
and proof that each of them appears infinitely many times in the sequence.

It will be shown that the sequence only contains the digits $2,4,6,8$ (i. e. the non-zero even digits)
and each of them infinitely many times.
-/

namespace BwM25R1A2

open scoped Nat

section Problem

/-! ## Definitions for setting up the problem -/

/-- The last non-zero decimal digit of `(n + 2)!`. -/
def lastDigitFac (n : ℕ) : ℕ := ((Nat.digits 10 (n + 2)!).find? (· ≠ 0)).get!

end Problem

-- ==============================

section Proof

/-! ## Lemmas and definitions for the proof -/

/-- The greatest `k : ℕ` such that `2 ^ k ≤ n`. -/
def maxTwoPowLe (n : ℕ) : ℕ := Nat.findGreatest (2 ^ · ≤ n) n

lemma zero_lt_maxTwoPowLe {n : ℕ} : 0 < maxTwoPowLe (n + 2) := by
  unfold maxTwoPowLe
  rw [Nat.findGreatest_pos]
  use 1
  simp

/-! ### Simplified factorization of natural numbers -/

/-- Describes a positive `n : ℕ` with (unique) `m₂ m₅ r : ℕ` such that `n = 2 ^ m₂ * 5 ^ m₅ * r` and
neither `2` nor `5` divides `r`. -/
@[ext]
structure SimpleFactorization : Type where
  /-- The amount of occurrences of the prime factor `2` in the factorization of the number. -/
  m₂ : ℕ
  /-- The amount of occurrences of the prime factor `5` in the factorization of the number. -/
  m₅ : ℕ
  /-- The number that you get when you remove all occurrences of the prime factors `2` and `5` in the
  factorization of the number. -/
  r : ℕ
  hr : ¬2 ∣ r ∧ ¬5 ∣ r
deriving Repr

/-- Assigns `m` its `SimpleFactorization` (`0` is assigned a garbage value). -/
def destruct (m : ℕ) : SimpleFactorization where
  m₂ := m.factorization 2
  m₅ := m.factorization 5
  r := if m ≠ 0 then m / 2 ^ m.factorization 2 / 5 ^ m.factorization 5 else 1
  hr := by
    split_ifs with hm
    · constructor
      · rw [Nat.dvd_div_iff_mul_dvd ?_]
        · by_contra ha
          absurd dvd_of_mul_left_dvd ha
          exact Nat.not_dvd_ordCompl Nat.prime_two hm
        · apply Nat.dvd_div_of_mul_dvd
          apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
          · apply Nat.Coprime.pow
            decide
          · apply Nat.ordProj_dvd
          · apply Nat.ordProj_dvd
      · have h : m.factorization 5 = (m / 2 ^ m.factorization 2).factorization 5 := by
          rw [Nat.factorization_div (by apply Nat.ordProj_dvd)]
          simp
          rw [show Nat.factorization 2 5 = 0 by native_decide]
          simp
        rw [h]
        apply Nat.not_dvd_ordCompl Nat.prime_five
        rw [Nat.div_ne_zero_iff_of_dvd (by apply Nat.ordProj_dvd)]
        simp
        exact hm
    · simp

@[simp]
lemma destruct_r_ne_zero {x : SimpleFactorization} : x.r ≠ 0 := by
  by_contra ha
  absurd x.hr.left
  rw [ha]
  simp

/-- Reconstructs `m : ℕ` from its `SimpleFactorization` (`destruct m`). -/
def restruct (x : SimpleFactorization) : ℕ := 2 ^ x.m₂ * 5 ^ x.m₅ * x.r

@[simp]
lemma destruct_restruct {x : SimpleFactorization} : destruct (restruct x) = x := by
  have h₁ : (destruct (restruct x)).m₂ = x.m₂ := by
    unfold restruct destruct
    simp
    rw [show Nat.factorization 5 2 = 0 by native_decide, show Nat.factorization 2 2 = 1 by native_decide]
    rw [Nat.factorization_eq_zero_of_not_dvd x.hr.left]
    simp
  have h₂ : (destruct (restruct x)).m₅ = x.m₅ := by
    unfold restruct destruct
    simp
    rw [show Nat.factorization 2 5 = 0 by native_decide, show Nat.factorization 5 5 = 1 by native_decide]
    rw [Nat.factorization_eq_zero_of_not_dvd x.hr.right]
    simp
  ext
  · exact h₁
  · exact h₂
  · unfold restruct destruct at *
    simp at *
    rw [h₁, h₂]
    conv =>
      lhs
      left
      left
      rw [mul_assoc, mul_comm]
      left
      rw [mul_comm]
    simp

@[simp]
lemma restruct_destruct {m : ℕ} : restruct (destruct (m + 1)) = m + 1 := by
  unfold destruct restruct
  simp
  conv =>
    lhs
    left
    rw [mul_comm]
  rw [mul_assoc, mul_comm, mul_assoc]
  rw [Nat.div_mul_cancel ?_]
  · rw [mul_comm]
    apply Nat.div_mul_cancel
    apply Nat.ordProj_dvd
  · apply Nat.dvd_div_of_mul_dvd
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    · apply Nat.Coprime.pow
      decide
    · apply Nat.ordProj_dvd
    · apply Nat.ordProj_dvd

/-! ### Elimination partners and pairs -/

/-- For a positive `m : ℕ`, `elimPartner m` is the number you get when you replace each appearence of the
prime factor `2` in the factorization of `m` with `5` and vice-versa. -/
def elimPartner (m : ℕ) : ℕ := let ⟨m₂, m₅, r, hr⟩ := destruct m; restruct ⟨m₅, m₂, r, hr⟩

@[simp]
lemma elimPartner_elimPartner {m : ℕ} : elimPartner (elimPartner (m + 1)) = m + 1 := by
  unfold elimPartner
  simp
  exact restruct_destruct

@[simp]
lemma elimPartner_eq_elimPartner {m m' : ℕ} : elimPartner (m + 1) = elimPartner (m' + 1) ↔ m = m' := by
  constructor
  · intro h
    have h' : elimPartner (elimPartner (m + 1)) = elimPartner (elimPartner (m' + 1)) := congr_arg _ h
    simp at h'
    exact h'
  · intro h
    rw [h]

@[simp]
lemma destruct_elimPartner₁ {m : ℕ} : (destruct (elimPartner m)).m₅ = (destruct m).m₂ := by
  unfold elimPartner
  simp

@[simp]
lemma destruct_elimPartner₂ {m : ℕ} : (destruct (elimPartner m)).m₂ = (destruct m).m₅ := by
  unfold elimPartner
  simp

@[simp]
lemma destruct_elimPartner₃ {m : ℕ} : (destruct (elimPartner m)).r = (destruct m).r := by
  unfold elimPartner
  simp

@[simp]
lemma elimPartner_sub_one_add_one {m : ℕ} : elimPartner (m + 1) - 1 + 1 = elimPartner (m + 1) := by
  apply Nat.sub_one_add_one
  rw [← restruct_destruct]
  unfold elimPartner restruct
  simp

lemma eq_elimPartner_self {m : ℕ} : (destruct (m + 1)).m₅ = (destruct (m + 1)).m₂ ↔
    elimPartner (m + 1) = m + 1 := by
  constructor
  · intro h
    unfold elimPartner
    simp
    rw [h]
    rw (config := { occs := .pos [2] }) [← h]
    rw [restruct_destruct]
  · intro h
    rw (config := { occs := .pos [1] }) [← h]
    simp

/-- If the factorization of `m + 1` contains the prime factor `2` at least as often as `5` and `m < n`,
then also `elimPartner (m + 1) - 1 < n`. -/
lemma elimPartner_mem_range {n m : ℕ} (h₁ : (destruct (m + 1)).m₂ < (destruct (m + 1)).m₅)
    (h₂ : m ∈ Finset.range n) : elimPartner (m + 1) - 1 ∈ Finset.range n := by
  rw [Finset.mem_range] at h₂ ⊢
  refine lt_trans ?_ h₂
  rw [← Nat.add_one_lt_add_one_iff]
  conv =>
    congr
    <;> rw [← restruct_destruct]
  rw [elimPartner_sub_one_add_one]
  unfold restruct
  simp
  apply Nat.mul_lt_mul_of_pos_right
  · rw [← Nat.sub_add_cancel h₁.le]
    conv =>
      lhs
      rw [pow_add, mul_assoc, ← mul_pow]
    conv =>
      rhs
      rw [pow_add, ← mul_assoc, mul_comm, ← mul_assoc, ← mul_pow, mul_comm]
    apply Nat.mul_lt_mul_of_pos_right
    · rw [Nat.pow_lt_pow_iff_left (Nat.sub_ne_zero_of_lt h₁)]
      simp
    · simp
  · apply Nat.zero_lt_of_ne_zero
    simp

/-- If `m < n + 2`, then `elimPartner (m + 1) - 1 ≠ 2 ^ maxTwoPowLe (n + 2) - 1`. -/
lemma elimPartner_ne_two_pow_of_mem_range {n m : ℕ} (h : m ∈ Finset.range (n + 2)) :
    elimPartner (m + 1) - 1 ≠ 2 ^ maxTwoPowLe (n + 2) - 1 := by
  by_contra ha
  conv at ha =>
    rw [← Nat.add_one_inj, Nat.sub_one_add_one (show 2 ^ _ ≠ 0 by simp)]
    simp
    rw [show 2 ^ _ = restruct ⟨maxTwoPowLe (n + 2), 0, 1, by simp⟩ by unfold restruct; simp]
  have ha := congr_arg elimPartner ha
  conv at ha =>
    simp
    unfold elimPartner
    simp
    unfold restruct
    simp
  have h' : 2 ^ (2 * maxTwoPowLe (n + 2)) ≤ n + 2 := by
    rw [pow_mul]
    calc
      _ ≤ 5 ^ maxTwoPowLe (n + 2) := by
        rw [Nat.pow_le_pow_iff_left (by rw [Nat.ne_zero_iff_zero_lt]; apply zero_lt_maxTwoPowLe)]; simp
      _ = m + 1 := ha.symm
      _ ≤ n + 2 := by rw [Nat.add_one_le_iff, ← Finset.mem_range]; exact h
  absurd show ¬2 ^ (2 * maxTwoPowLe (n + 2)) ≤ n + 2 by
    apply @Nat.findGreatest_is_greatest (2 * maxTwoPowLe (n + 2)) (2 ^ · ≤ n + 2) _ (n + 2)
    · refine (Nat.lt_mul_iff_one_lt_left ?_).mpr ?_
      · exact zero_lt_maxTwoPowLe
      · simp
    · apply le_of_lt
      calc
       _ < 2 ^ (2 * maxTwoPowLe (n + 2)) := by exact Nat.lt_two_pow_self
       _ ≤ n + 2 := h'
  exact h'

/-- The set of `m : ℕ` with `m < n` such that in `m + 1`, the prime factor `2` appears at least as often
as the prime factor `5` but `m ≠ maxTwoPowLe n - 1`. -/
def setOfM₅LeM₂SubOne (n : ℕ) : Finset ℕ :=
  {m ∈ Finset.range n | (destruct (m + 1)).m₅ ≤ (destruct (m + 1)).m₂ ∧ m ≠ 2 ^ maxTwoPowLe n - 1}

/-- For `m ∈ setOfM₅LeM₂SubOne n`, `elimPairSubOne n m` will contains `m` and - if
`elimPartner (m + 1) ≤ n` - also `elimPartner (m + 1) - 1`. -/
def elimPairSubOne (n m : ℕ) : Finset ℕ := {m, elimPartner (m + 1) - 1} ∩ Finset.range n

lemma elimPair_eq_singleton_or_pair {n m : ℕ} (hm : m ∈ setOfM₅LeM₂SubOne n) : elimPairSubOne n m = {m} ∨
    (elimPairSubOne n m = {m, elimPartner (m + 1) - 1} ∧ m ≠ elimPartner (m + 1) - 1) := by
  unfold setOfM₅LeM₂SubOne at hm
  rw [Finset.mem_filter] at hm
  by_cases h : (destruct (m + 1)).m₅ = (destruct (m + 1)).m₂
  · apply Or.inl
    apply Finset.Subset.antisymm
    · calc
        _ ⊆ {m, elimPartner (m + 1) - 1} := Finset.inter_subset_left
        _ = {m} := by rw [eq_elimPartner_self.mp h]; simp
    · unfold elimPairSubOne
      simp [-Finset.mem_range]
      exact hm.left
  · by_cases h' : elimPartner (m + 1) - 1 ∈ Finset.range n
    · apply Or.inr
      constructor
      · apply Finset.Subset.antisymm
        · exact Finset.inter_subset_left
        · apply Finset.subset_inter Finset.Subset.rfl
          rw [Finset.insert_eq, Finset.union_subset_iff]
          rw [Finset.singleton_subset_iff, Finset.singleton_subset_iff]
          exact ⟨hm.left, h'⟩
      · by_contra ha
        conv at ha =>
          rw [eq_comm, ← Nat.add_one_inj]
          simp
          rw [← eq_elimPartner_self]
        absurd ha
        exact h
    · apply Or.inl
      apply Finset.Subset.antisymm
      · unfold elimPairSubOne
        rw [Finset.insert_eq, Finset.union_inter_distrib_right, Finset.singleton_inter_of_notMem h']
        rw [Finset.union_empty]
        exact Finset.inter_subset_left
      · unfold elimPairSubOne
        simp [-Finset.mem_range]
        exact hm.left

/-! ### Factorization of factorials -/

lemma factorization_factorial_eq_sum {n p : ℕ} : Nat.factorization (n + 2)! p =
    ∑ m ∈ Finset.range (n + 2), Nat.factorization (m + 1) p := by
  rw [← Finset.prod_range_add_one_eq_factorial]
  rw [← Finset.sum_apply, ← Finsupp.coe_finset_sum, ← Nat.factorization_prod]
  simp

lemma sum_factorization_erase_two_pow {n p : ℕ} : let k := maxTwoPowLe (n + 2)
    ∑ m ∈ Finset.range (n + 2), Nat.factorization (m + 1) p =
    ∑ m ∈ (Finset.range (n + 2)).erase (2 ^ k - 1), Nat.factorization (m + 1) p +
    Nat.factorization (2 ^ k) p := by
  intro k
  have h : 2 ^ k - 1 ∈ Finset.range (n + 2) := by
    rw [Finset.mem_range]
    apply Nat.sub_one_lt_of_le (by simp)
    exact @Nat.findGreatest_spec 0 (2 ^ · ≤ n + 2) _ _ (by simp) (by simp)
  rw [eq_comm]
  rw (config := { occs := .pos [2] }) [← Nat.sub_one_add_one (show 2 ^ k ≠ 0 by simp)]
  apply Finset.sum_erase_add
  exact h

/-- The set of `m < n + 2` without `2 ^ maxTwoPowLe (n + 2) - 1` can be described as the union of
`elimPairSubOne (n + 2) m` for all `m ∈ setOfM₅LeM₂SubOne (n + 1)`. -/
lemma range_erase_eq_biUnion {n : ℕ} : (Finset.range (n + 2)).erase (2 ^ maxTwoPowLe (n + 2) - 1) =
    Finset.biUnion (setOfM₅LeM₂SubOne (n + 2)) (elimPairSubOne (n + 2)) := by
  apply Finset.ext
  intro m
  rw [Finset.mem_biUnion, Finset.mem_erase]
  constructor
  · intro hm
    by_cases h : (destruct (m + 1)).m₅ ≤ (destruct (m + 1)).m₂
    · use m
      constructor
      · unfold setOfM₅LeM₂SubOne
        rw [Finset.mem_filter]
        exact ⟨hm.right, ⟨h, hm.left⟩⟩
      · exact Finset.mem_inter_of_mem (by simp) hm.right
    · rw [not_le] at h
      use elimPartner (m + 1) - 1
      constructor
      · unfold setOfM₅LeM₂SubOne
        rw [Finset.mem_filter]
        refine ⟨?_, ⟨?_, ?_⟩⟩
        · exact elimPartner_mem_range h hm.right
        · simp
          apply le_of_lt
          exact h
        · exact elimPartner_ne_two_pow_of_mem_range hm.right
      · refine Finset.mem_inter_of_mem ?_ hm.right
        simp
  · intro ⟨m', hm', hmm'⟩
    constructor
    · unfold setOfM₅LeM₂SubOne at hm'
      rw [Finset.mem_filter] at hm'
      unfold elimPairSubOne at hmm'
      rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hmm'
      cases hmm'.left with
      | inl hmm' =>
        rw [hmm']
        exact hm'.right.right
      | inr hmm' =>
        rw [hmm']
        exact elimPartner_ne_two_pow_of_mem_range hm'.left
    · exact Finset.mem_of_mem_inter_right hmm'

lemma ne_elimPartner_of_mem_of_ne {n x y : ℕ} (hx : x ∈ setOfM₅LeM₂SubOne n)
    (hy : y ∈ setOfM₅LeM₂SubOne n) (hxy : x ≠ y) : x ≠ elimPartner (y + 1) - 1 := by
  by_cases h : (destruct (y + 1)).m₂ = (destruct (y + 1)).m₅
  · unfold elimPartner
    simp
    rw [h]
    rw (config := { occs := .pos [1] }) [← h]
    rw [restruct_destruct]
    simp
    exact hxy
  · by_contra ha
    conv at hx =>
      rw [ha]
      unfold setOfM₅LeM₂SubOne
      rw [Finset.mem_filter]
    absurd hx.right.left
    simp
    apply lt_of_le_of_ne
    · conv at hy =>
        unfold setOfM₅LeM₂SubOne
        rw [Finset.mem_filter]
      exact hy.right.left
    · rw [ne_comm]
      exact h

/-- The sets `elimPairSubOne n m` are pairwise disjoint. -/
lemma pairwiseDisjoint_elimPair {n : ℕ} : (setOfM₅LeM₂SubOne n : Set ℕ).PairwiseDisjoint
    (elimPairSubOne n) := by
  intros x hx y hy hxy
  rw [Finset.mem_coe] at hx hy
  unfold Function.onFun
  rw [Finset.disjoint_iff_ne]
  intros x' hx' y' hy'
  unfold elimPairSubOne at hx' hy'
  rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx' hy'
  cases hx'.left with
  | inl hxx' =>
    cases hy'.left with
    | inl hyy' =>
      rw [hxx', hyy']
      exact hxy
    | inr hyy' =>
      rw [hxx', hyy']
      exact ne_elimPartner_of_mem_of_ne hx hy hxy
  | inr hxx' =>
    cases hy'.left with
    | inl hyy' =>
      rw [hxx', hyy', ne_comm]
      exact ne_elimPartner_of_mem_of_ne hy hx hxy.symm
    | inr hyy' =>
      rw [hxx', hyy']
      by_contra ha
      rw [← Nat.add_one_inj] at ha
      simp at ha
      absurd ha
      exact hxy

lemma factorization_factorial_five_lt_two {n : ℕ} : Nat.factorization (n + 2)! 5 <
    Nat.factorization (n + 2)! 2 := by
  conv =>
    args
    <;> rw [factorization_factorial_eq_sum, sum_factorization_erase_two_pow]
  set k := maxTwoPowLe (n + 2)
  rw [Finset.sum_congr rfl (show ∀ m ∈ _, (m + 1).factorization 5 = (destruct (m + 1)).m₅ by intros _ _; rfl)]
  rw [Finset.sum_congr rfl (show ∀ m ∈ _, (m + 1).factorization 2 = (destruct (m + 1)).m₂ by intros _ _; rfl)]
  apply add_lt_add_of_le_of_lt
  · rw [range_erase_eq_biUnion, Finset.sum_biUnion pairwiseDisjoint_elimPair]
    rw [Finset.sum_biUnion pairwiseDisjoint_elimPair]
    apply Finset.sum_le_sum
    intros m hm
    cases elimPair_eq_singleton_or_pair hm with
    | inl h =>
      rw [h, Finset.sum_singleton, Finset.sum_singleton]
      unfold setOfM₅LeM₂SubOne at hm
      rw [Finset.mem_filter] at hm
      exact hm.right.left
    | inr h =>
      rw [h.left, Finset.sum_pair h.right, Finset.sum_pair h.right, add_comm]
      apply le_of_eq
      simp
  · rw [Nat.Prime.factorization_pow Nat.prime_two]
    simp
    unfold k maxTwoPowLe
    rw [Nat.findGreatest_pos]
    use 1
    simp

/-- This lemma will help us in both parts of the problem. -/
lemma last_nonzero_digit_eq {l : ℕ} (hl : l ≠ 0) (hm₅m₂ : l.factorization 5 < l.factorization 2) :
    ((Nat.digits 10 l).find? (· ≠ 0)).get! = l / 10 ^ l.factorization 5 % 10 := by
  let rec aux (k : ℕ) {l : ℕ} (hl : l ≠ 0) (hm₅m₂ : l.factorization 5 < l.factorization 2)
      (hk : l.factorization 5 = k) :
      ((Nat.digits 10 l).find? (· ≠ 0)).get! = l / 10 ^ k % 10 := by
    rw [Nat.digits_def' (by simp) (Nat.zero_lt_of_ne_zero hl), List.find?_cons]
    rw [ne_eq] at hl
    match k with
    | 0 =>
      have h : l % 10 ≠ 0 := by
        rw [ne_eq, ← Nat.dvd_iff_mod_eq_zero, show 10 = 2 * 5 by rfl]
        by_contra ha
        have ha : 5 ∣ l := dvd_of_mul_left_dvd ha
        absurd ha
        rw [Nat.factorization_eq_zero_iff, eq_true Nat.prime_five, eq_false hl] at hk
        simp at hk
        exact hk
      rw [decide_eq_true h]
      simp
    | k + 1 =>
      have h : ¬l % 10 ≠ 0 := by
        rw [ne_eq, not_not, ← Nat.dvd_iff_mod_eq_zero, show 10 = 2 * 5 by rfl]
        apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
        · decide
        · have h' : l.factorization 2 ≠ 0 := by
            rw [Nat.ne_zero_iff_zero_lt]
            apply Nat.zero_lt_of_lt
            exact hm₅m₂
          rw [ne_eq, Nat.factorization_eq_zero_iff, eq_true Nat.prime_two, eq_false hl] at h'
          rw [not_true, false_or, or_false, not_not] at h'
          exact h'
        · have h' : l.factorization 5 ≠ 0 := by
            rw [hk]
            simp
          rw [ne_eq, Nat.factorization_eq_zero_iff, eq_true Nat.prime_five, eq_false hl] at h'
          rw [not_true, false_or, or_false, not_not] at h'
          exact h'
      rw [decide_eq_false h, Nat.pow_add_one, mul_comm, ← Nat.div_div_eq_div_mul]
      rw [ne_eq, not_not, ← Nat.dvd_iff_mod_eq_zero] at h
      have l_div_ten_ne_zero : l / 10 ≠ 0 := by
        rw [Nat.div_ne_zero_iff_of_dvd h]
        exact ⟨hl, by simp⟩
      have h_factorization_five : (l / 10).factorization 5 + 1 = l.factorization 5 := by
        rw [show 1 = Nat.factorization 10 5 by native_decide, ← Finsupp.add_apply]
        rw [← Nat.factorization_mul l_div_ten_ne_zero (show 10 ≠ 0 by simp)]
        rw [Nat.div_mul_cancel h]
      have h_factorization_two : (l / 10).factorization 2 + 1 = l.factorization 2 := by
        rw [show 1 = Nat.factorization 10 2 by native_decide, ← Finsupp.add_apply]
        rw [← Nat.factorization_mul l_div_ten_ne_zero (show 10 ≠ 0 by simp)]
        rw [Nat.div_mul_cancel h]
      refine aux k l_div_ten_ne_zero ?_ ?_
      · rw [← Nat.add_one_lt_add_one_iff]
        rw [h_factorization_five, h_factorization_two]
        exact hm₅m₂
      · rw [← Nat.add_one_inj, h_factorization_five]
        exact hk
  exact aux (l.factorization 5) hl hm₅m₂ (by simp)

/-- If `l ≠ 0` and the factorization of `l` contains the prime factor `2` more often than `5`, then the
last non-zero digit of the decimal representation of `l` is even. -/
lemma even_last_non_zero_digit_of_factorization_five_lt_two {l : ℕ} (hl : l ≠ 0)
    (hm₅m₂ : l.factorization 5 < l.factorization 2) :
    ((Nat.digits 10 l).find? (· ≠ 0)).get! % 2 = 0 := by
  rw [last_nonzero_digit_eq hl hm₅m₂, Nat.mod_mod_of_dvd _ (by simp), ← Nat.dvd_iff_mod_eq_zero]
  rw [show 10 = 5 * 2 by rfl, mul_pow]
  apply Nat.dvd_div_of_mul_dvd
  rw [mul_assoc, ← Nat.pow_add_one]
  apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
  · apply Nat.Coprime.pow
    decide
  · apply Nat.ordProj_dvd
  · rw [← Nat.add_one_le_iff] at hm₅m₂
    apply Nat.pow_dvd_of_le_of_pow_dvd hm₅m₂
    apply Nat.ordProj_dvd

lemma set_of_digits_subset_solution : {d | ∃ n, lastDigitFac n = d} ⊆ {2, 4, 6, 8} := by
  intro d ⟨n, hn⟩
  rw [← Finset.coe_singleton, ← Finset.coe_insert, ← Finset.coe_insert, ← Finset.coe_insert]
  show d ∈ {d ∈ Finset.range 10 | d ≠ 0 ∧ d % 2 = 0}
  simp
  have h : (Nat.digits 10 (n + 2)!).find? (· ≠ 0) = .some d := by
    rw [← hn, eq_comm]
    apply Option.some_get!
    rw [List.find?_isSome]
    use (Nat.digits 10 (n + 2)!).getLast
      (by rw [Nat.digits_ne_nil_iff_ne_zero]; exact Nat.factorial_ne_zero (n + 2))
    simp
    exact Nat.getLast_digit_ne_zero 10 (Nat.factorial_ne_zero (n + 2))
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · apply Nat.digits_lt_base (by simp) (show d ∈ Nat.digits 10 (n + 2)! from ?_)
    exact List.mem_of_find?_eq_some h
  · rw [← ne_eq, ← @decide_eq_true_iff (d ≠ 0)]
    exact @List.find?_some _ (· ≠ 0) _ _ h
  · rw [← hn]
    apply even_last_non_zero_digit_of_factorization_five_lt_two
      (show (n + 2)! ≠ 0 from Nat.factorial_ne_zero (n + 2))
    exact factorization_factorial_five_lt_two

/-! ### Lemmas for the second part of the problem -/

/-- We can determine the last non-zero digit of `l * n` using only the value of `n` and the last non-zero
digit of `l`. -/
lemma last_nonzero_digit_l_mul_n {l n : ℕ} (hl : l ≠ 0) (hm₅m₂ : l.factorization 5 < l.factorization 2)
    (hn : n % 5 ≠ 0) : ((Nat.digits 10 (l * n)).find? (· ≠ 0)).get! =
    ((Nat.digits 10 l).find? (· ≠ 0)).get! * (n % 10) % 10 := by
  have hn' : n ≠ 0 := by
    by_contra ha
    rw [ha] at hn
    simp at hn
  have hn'' : n.factorization 5 = 0 := by
    rw [ne_eq, ← Nat.dvd_iff_mod_eq_zero] at hn
    exact Nat.factorization_eq_zero_of_not_dvd hn
  have hl' : l * n ≠ 0 := Nat.mul_ne_zero hl hn'
  have hm₅m₂' : (l * n).factorization 5 < (l * n).factorization 2 := by
    rw [Nat.factorization_mul hl hn', Finsupp.add_apply, Finsupp.add_apply]
    apply add_lt_add_of_lt_of_le
    · exact hm₅m₂
    · rw [hn'']
      simp
  have h : (l * n).factorization 5 = l.factorization 5 := by
    rw [Nat.factorization_mul hl hn', Finsupp.add_apply, hn'']
    simp
  rw [last_nonzero_digit_eq hl' hm₅m₂', last_nonzero_digit_eq hl hm₅m₂, h]
  simp
  rw [Nat.mul_div_right_comm ?_]
  rw [show 10 = 2 * 5 by rfl, mul_pow]
  apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
  · apply Nat.Coprime.pow
    decide
  · apply Nat.pow_dvd_of_le_of_pow_dvd hm₅m₂.le
    apply Nat.ordProj_dvd
  · apply Nat.ordProj_dvd

lemma lastDigitFac_succ {n : ℕ} (h : (n + 3) % 5 ≠ 0) : lastDigitFac (n + 1) =
    lastDigitFac n * ((n + 3) % 10) % 10 := by
  unfold lastDigitFac
  rw [add_assoc, show 1 + 2 = 2 + 1 by rfl, ← add_assoc, Nat.factorial_succ, mul_comm]
  apply last_nonzero_digit_l_mul_n
  · apply Nat.factorial_ne_zero
  · exact factorization_factorial_five_lt_two
  · exact h

lemma n_lt {n k : ℕ} : n < 10 ^ (n + 1) - 6 + k := by
  apply Nat.lt_add_right k
  apply Nat.lt_sub_of_add_lt
  calc
    _ < 10 * (n + 1) := ?_
    _ ≤ 10 ^ (n + 1) := ?_
  · rw [left_distrib]
    apply add_lt_add_of_le_of_lt
    · apply Nat.le_mul_of_pos_left
      simp
    · simp
  · rw [Nat.pow_add_one, mul_comm]
    apply Nat.mul_le_mul_right
    rw [Nat.add_one_le_iff]
    apply Nat.lt_pow_self
    simp

@[simp]
lemma six_le_ten_pow {n : ℕ} : 6 ≤ 10 ^ (n + 1) := by
  rw [Nat.pow_add_one]
  calc
    _ ≤ 10 := by simp
    _ ≤ 10 ^ n * 10 := Nat.le_mul_of_pos_left _ (by simp)

lemma ten_pow_add_mod_five {n k : ℕ} : (10 ^ (n + 1) - 6 + k) % 5 = (4 + k) % 5 := by
  apply Nat.add_mod_eq_add_mod_right
  rw [← Nat.add_mod_right, ← Nat.add_mod_right]
  conv =>
    lhs
    left
    rw [add_assoc, show 5 + 5 = 6 + 4 by rfl, ← add_assoc]
  rw [Nat.sub_add_cancel ?_]
  · apply Nat.add_mod_eq_add_mod_right
    rw [← Nat.dvd_iff_mod_eq_zero, Nat.pow_add_one, show 10 = 2 * 5 by rfl, ← mul_assoc]
    simp
  · simp

lemma ten_pow_add_mod_ten {n k : ℕ} : (10 ^ (n + 1) - 6 + k) % 10 = (4 + k) % 10 := by
  apply Nat.add_mod_eq_add_mod_right
  rw [← Nat.add_mod_right]
  conv =>
    lhs
    left
    right
    rw [show 10 = 6 + 4 by rfl]
  rw [← add_assoc, Nat.sub_add_cancel ?_]
  · rw [Nat.add_mod]
    conv =>
      lhs
      left
      left
      rw [Nat.mod_eq_zero_of_dvd (by rw [Nat.pow_add_one]; simp)]
  · simp

/-- The last non-zero digits of `l * 10 ^ k` and `l` are equal. -/
lemma last_nonzero_digit_mul_ten_pow {l k : ℕ} (hl : l ≠ 0)
    (hm₅m₂ : l.factorization 5 < l.factorization 2) : ((Nat.digits 10 (l * 10 ^ k)).find? (· ≠ 0)).get! =
    ((Nat.digits 10 l).find? (· ≠ 0)).get! := by
  rw [last_nonzero_digit_eq, last_nonzero_digit_eq]
  · conv =>
      lhs
      left
      right
      rw [Nat.factorization_mul hl (by simp)]
      rw (config := { occs := .pos [2] }) [show 10 = 2 * 5 by rfl]
      rw [mul_pow, Nat.factorization_mul (by simp) (by simp)]
      simp
      rw [show Nat.factorization 2 5 = 0 by native_decide]
      rw [show Nat.factorization 5 5 = 1 by native_decide]
      simp
      rw [pow_add, mul_comm]
    rw [← Nat.div_div_eq_div_mul]
    simp
  · exact hl
  · exact hm₅m₂
  · simp
    exact hl
  · rw [show 10 = 2 * 5 by rfl, mul_pow]
    rw [Nat.factorization_mul, Nat.factorization_mul]
    · simp
      rw [show Nat.factorization 2 5 = 0 by native_decide]
      rw [show Nat.factorization 5 5 = 1 by native_decide]
      rw [show Nat.factorization 2 2 = 1 by native_decide]
      rw [show Nat.factorization 5 2 = 0 by native_decide]
      simp
      exact hm₅m₂
    · simp
    · simp
    · exact hl
    · simp

/-! ### Considering every possible case for finding an occurrence of a digit -/

lemma lastDigitFac_add_one {n : ℕ} : lastDigitFac (10 ^ (n + 1) - 6 + 1) =
    lastDigitFac (10 ^ (n + 1) - 6) * 7 % 10 := by
  rw [lastDigitFac_succ ?_, ten_pow_add_mod_ten]
  rw [ne_eq, ten_pow_add_mod_five]
  simp

lemma lastDigitFac_add_two {n : ℕ} : lastDigitFac (10 ^ (n + 1) - 6 + 2) =
    lastDigitFac (10 ^ (n + 1) - 6) * 6 % 10 := by
  rw [lastDigitFac_succ ?_, lastDigitFac_add_one, add_assoc, ten_pow_add_mod_ten]
  · simp
    rw [mul_assoc, Nat.mul_mod]
    simp
  · rw [add_assoc, ne_eq, ten_pow_add_mod_five]
    simp

lemma lastDigitFac_add_three {n : ℕ} : lastDigitFac (10 ^ (n + 1) - 6 + 3) =
    lastDigitFac (10 ^ (n + 1) - 6) * 4 % 10 := by
  rw [lastDigitFac_succ ?_, lastDigitFac_add_two, add_assoc, ten_pow_add_mod_ten]
  · simp
    rw [mul_assoc, Nat.mul_mod]
    simp
  · rw [add_assoc, ne_eq, ten_pow_add_mod_five]
    simp

lemma lastDigitFac_ten_pow {n : ℕ} : lastDigitFac (10 ^ (n + 1) - 6 + 4) =
    lastDigitFac (10 ^ (n + 1) - 6 + 3) := by
  have h : 3 ≤ 10 ^ (n + 1) - 3 := by
    apply Nat.le_sub_of_add_le
    simp
  have h' : 3 ≤ 10 ^ (n + 1) := by
    calc
      _ ≤ 10 ^ (n + 1) - 3 := h
      _ ≤ 10 ^ (n + 1) := by simp
  rw [show 6 = 3 + 3 by rfl, ← Nat.sub_sub]
  conv =>
    lhs
    rw [← Nat.sub_add_comm h, Nat.add_sub_assoc (by simp)]
  conv =>
    rhs
    rw [← Nat.sub_add_comm h, Nat.add_sub_assoc (by simp)]
  simp
  unfold lastDigitFac
  rw [Nat.factorial_succ, add_assoc, Nat.sub_add_cancel h', mul_comm]
  apply last_nonzero_digit_mul_ten_pow
  · apply Nat.factorial_ne_zero
  · exact factorization_factorial_five_lt_two

lemma lastDigitFac_add_five {n : ℕ} : lastDigitFac (10 ^ (n + 1) - 6 + 5) =
    lastDigitFac (10 ^ (n + 1) - 6) * 4 % 10 := by
  rw [lastDigitFac_succ ?_, lastDigitFac_ten_pow, lastDigitFac_add_three, add_assoc, ten_pow_add_mod_ten]
  · simp
  · rw [add_assoc, ne_eq, ten_pow_add_mod_five]
    simp

lemma lastDigitFac_add_six {n : ℕ} : lastDigitFac (10 ^ (n + 1) - 6 + 6) =
    lastDigitFac (10 ^ (n + 1) - 6) * 8 % 10 := by
  rw [lastDigitFac_succ ?_, lastDigitFac_add_five, add_assoc, ten_pow_add_mod_ten]
  · simp
    rw [mul_assoc, Nat.mul_mod]
    simp
  · rw [add_assoc, ne_eq, ten_pow_add_mod_five]
    simp

lemma exists_with_lastDigitFac_add_zero {n d : ℕ} (h : d = lastDigitFac (10 ^ (n + 1) - 6)) :
    ∃ m ∈ {m | lastDigitFac m = d}, n < m := by
  use 10 ^ (n + 1) - 6 + 0
  refine ⟨?_, n_lt⟩
  simp
  rw [h]

lemma exists_with_lastDigitFac_add_one {n d : ℕ} (h : d = lastDigitFac (10 ^ (n + 1) - 6) * 7 % 10) :
    ∃ m ∈ {m | lastDigitFac m = d}, n < m := by
  use 10 ^ (n + 1) - 6 + 1
  refine ⟨?_, n_lt⟩
  rw [h]
  exact lastDigitFac_add_one

lemma exists_with_lastDigitFac_add_two {n d : ℕ} (h : d = lastDigitFac (10 ^ (n + 1) - 6) * 6 % 10) :
    ∃ m ∈ {m | lastDigitFac m = d}, n < m := by
  use 10 ^ (n + 1) - 6 + 2
  refine ⟨?_, n_lt⟩
  rw [h]
  exact lastDigitFac_add_two

lemma exists_with_lastDigitFac_add_three {n d : ℕ} (h : d = lastDigitFac (10 ^ (n + 1) - 6) * 4 % 10) :
    ∃ m ∈ {m | lastDigitFac m = d}, n < m := by
  use 10 ^ (n + 1) - 6 + 3
  refine ⟨?_, n_lt⟩
  rw [h]
  exact lastDigitFac_add_three

lemma exists_with_lastDigitFac_add_six {n d : ℕ} (h : d = lastDigitFac (10 ^ (n + 1) - 6) * 8 % 10) :
    ∃ m ∈ {m | lastDigitFac m = d}, n < m := by
  use 10 ^ (n + 1) - 6 + 6
  refine ⟨?_, n_lt⟩
  rw [h]
  exact lastDigitFac_add_six

/-- For every digit `d ∈ {2, 4, 6, 8}` any `n : ℕ`, we can find an `m : ℕ` with `n < m` such that
`lastDigitFac m = d`, thus proving that each of these digits appears infinitely often in
`lastDigitFac`. -/
lemma exists_with_lastDigitFac_eq {d n : ℕ} (hd : d ∈ ({2, 4, 6, 8} : Set ℕ)) :
    ∃ m ∈ {m | lastDigitFac m = d}, n < m := by
  have h : lastDigitFac (10 ^ (n + 1) - 6) ∈ ({2, 4, 6, 8} : Set ℕ) := by
    apply Set.mem_of_subset_of_mem set_of_digits_subset_solution
    simp
  obtain hd | hd | hd | hd := hd
  · rw [hd]
    obtain h | h | h | h := h
    · apply exists_with_lastDigitFac_add_zero
      rw [h]
    · apply exists_with_lastDigitFac_add_six
      rw [h]
    · apply exists_with_lastDigitFac_add_one
      rw [h]
    · apply exists_with_lastDigitFac_add_three
      rw [h]
  · rw [hd]
    obtain h | h | h | h := h
    · apply exists_with_lastDigitFac_add_one
      rw [h]
    · apply exists_with_lastDigitFac_add_zero
      rw [h]
    · apply exists_with_lastDigitFac_add_three
      rw [h]
    · apply exists_with_lastDigitFac_add_six
      rw [h]
  · rw [hd]
    obtain h | h | h | h := h
    · apply exists_with_lastDigitFac_add_six
      rw [h]
    · apply exists_with_lastDigitFac_add_three
      rw [h]
    · apply exists_with_lastDigitFac_add_two
      rw [h]
    · apply exists_with_lastDigitFac_add_one
      rw [h]
  · rw [hd]
    obtain h | h | h | h := h
    · apply exists_with_lastDigitFac_add_three
      rw [h]
    · apply exists_with_lastDigitFac_add_one
      rw [h]
    · apply exists_with_lastDigitFac_add_six
      rw [h]
    · apply exists_with_lastDigitFac_add_zero
      rw [h]

end Proof

-- ==============================

section Result

/-! ## The solution and the proof of its correctness -/

/-- The set of digits in the sequence. -/
def solution : Set ℕ := {2, 4, 6, 8}

/-- Proof that the above `solution` is correct. -/
theorem proof : solution = {d | ∃ n, lastDigitFac n = d} ∧
    ∀ d ∈ solution, Set.Infinite {n | lastDigitFac n = d} := by
  constructor
  · apply Set.eq_of_subset_of_subset
    · apply Set.insert_subset (by use 0; native_decide)
      apply Set.insert_subset (by use 2; native_decide)
      apply Set.insert_subset (by use 1; native_decide)
      rw [Set.singleton_subset_iff]; use 7; native_decide
    · exact set_of_digits_subset_solution
  · intros d hd
    apply Set.infinite_of_forall_exists_gt
    intro n
    exact exists_with_lastDigitFac_eq hd

end Result

end BwM25R1A2
