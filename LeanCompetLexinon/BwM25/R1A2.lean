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

## TODO
* Second part of the problem
* Add comments
* Split up longer tactic proofs
-/

namespace BwM25R1A2

open scoped Nat

section Problem

/-! ## Definitions for setting up the problem -/

def lastDigitFac (n : ℕ) : ℕ := ((Nat.digits 10 (n + 2)!).find? (· ≠ 0)).get!

end Problem

-- ==============================

section Proof

/-! ## Lemmas and definitions for the proof -/

def maxTwoPowLe (n : ℕ) : ℕ := Nat.findGreatest (2 ^ · ≤ n) n

@[simp]
lemma zero_lt_maxTwoPowLe {n : ℕ} : 0 < maxTwoPowLe (n + 2) := by
  unfold maxTwoPowLe
  rw [Nat.findGreatest_pos]
  use 1
  simp

@[ext]
structure SimpleFactorization : Type where
  m₂ : ℕ
  m₅ : ℕ
  r : ℕ
  hr : ¬2 ∣ r ∧ ¬5 ∣ r
deriving Repr

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

def restruct (x : SimpleFactorization) : ℕ := 5 ^ x.m₅ * 2 ^ x.m₂ * x.r

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
      left
      rw [mul_comm]
    rw [mul_assoc]
    simp

@[simp]
lemma restruct_destruct {m : ℕ} : restruct (destruct (m + 1)) = m + 1 := by
  unfold destruct restruct
  simp
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

def setOfM₅LeM₂SubOne (n : ℕ) : Finset ℕ :=
  {m ∈ Finset.range n | (destruct (m + 1)).m₅ ≤ (destruct (m + 1)).m₂ ∧ m ≠ 2 ^ maxTwoPowLe n - 1}

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

def elimPairSubOne (n m : ℕ) : Finset ℕ := {m, elimPartner (m + 1) - 1} ∩ Finset.range n

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
      rw [pow_add, mul_comm, mul_assoc, ← mul_pow]
    conv =>
      rhs
      rw [pow_add, mul_assoc, ← mul_pow]
    apply Nat.mul_lt_mul_of_pos_right
    · rw [Nat.pow_lt_pow_iff_left (Nat.sub_ne_zero_of_lt h₁)]
      simp
    · simp
  · apply Nat.zero_lt_of_ne_zero
    simp

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
        rw [Nat.pow_le_pow_iff_left (by rw [Nat.ne_zero_iff_zero_lt]; simp)]; simp
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

lemma even_last_non_zero_digit_of_factorization_five_lt_two {l : ℕ} (hl : l ≠ 0)
    (hm₅m₂ : l.factorization 5 < l.factorization 2) :
    ((Nat.digits 10 l).find? (· ≠ 0)).get! % 2 = 0 := by
  let rec aux (m₅ : ℕ) {l : ℕ} (hl : l ≠ 0) (hm₅m₂ : l.factorization 5 < l.factorization 2) (hm₅ : l.factorization 5 = m₅) : ((Nat.digits 10 l).find? (· ≠ 0)).get! % 2 = 0 := by
    have bla' : l.factorization 2 ≠ 0 := Nat.ne_zero_of_lt hm₅m₂
    conv at bla' =>
      rw [ne_eq, Nat.factorization_eq_zero_iff]
      simp
    have bla' : l % 2 = 0 := bla'.right.left
    match m₅ with
    | 0 =>
      have bla : l % 10 ≠ 0 := by
        conv at hm₅ =>
          unfold destruct
          rw [Nat.factorization_eq_zero_iff, eq_true Nat.prime_five, eq_false hl]
          simp
        rw [ne_eq, ← Nat.dvd_iff_mod_eq_zero, show 10 = 2 * 5 by rfl]
        by_contra ha
        absurd dvd_of_mul_left_dvd ha
        exact hm₅
      rw [Nat.digits_def' (by simp) (Nat.zero_lt_of_ne_zero hl), List.find?_cons, decide_eq_true bla]
      simp
      exact bla'
    | m₅ + 1 =>
      have bla : ¬l % 10 ≠ 0 := by
        rw [ne_eq, not_not, ← Nat.dvd_iff_mod_eq_zero, show 10 = 2 * 5 by rfl]
        apply Nat.Prime.dvd_mul_of_dvd_ne (by simp) Nat.prime_two Nat.prime_five
        · rw [Nat.dvd_iff_mod_eq_zero]
          exact bla'
        · have hm₅' : l.factorization 5 ≠ 0 := by
            rw [hm₅]
            simp
          conv at hm₅' =>
            unfold destruct
            rw [ne_eq, Nat.factorization_eq_zero_iff]
            simp
          exact hm₅'.right.left
      rw [Nat.digits_def' (by simp) (Nat.zero_lt_of_ne_zero hl), List.find?_cons, decide_eq_false bla]
      simp only
      rw [ne_eq, not_not, ← Nat.dvd_iff_mod_eq_zero] at bla
      have l_div_ten_ne_zero : l / 10 ≠ 0 := by
        rw [Nat.div_ne_zero_iff_of_dvd bla]
        simp
        exact hl
      have m₂_add_one_eq_m₂ : (l / 10).factorization 2 + 1 = l.factorization 2 := by
        rw [show 1 = Nat.factorization 10 2 by native_decide]
        rw (config := { occs := .pos [2] }) [← show l / 10 * 10 = l from Nat.div_mul_cancel bla]
        rw [Nat.factorization_mul l_div_ten_ne_zero (by simp)]
        simp
      have m₅_add_one_eq_m₅ : (l / 10).factorization 5 + 1 = l.factorization 5 := by
        rw [show 1 = Nat.factorization 10 5 by native_decide]
        rw (config := { occs := .pos [2] }) [← show l / 10 * 10 = l from Nat.div_mul_cancel bla]
        rw [Nat.factorization_mul l_div_ten_ne_zero (by simp)]
        simp
      refine aux m₅ l_div_ten_ne_zero ?_ ?_
      · rw [← Nat.add_one_lt_add_one_iff]
        rw [m₂_add_one_eq_m₂, m₅_add_one_eq_m₅]
        exact hm₅m₂
      · rw [← Nat.add_one_inj, ← hm₅]
        exact m₅_add_one_eq_m₅
  exact aux (l.factorization 5) hl hm₅m₂ (by simp)

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
    · intro d ⟨n, hn⟩
      unfold solution
      rw [← Finset.coe_singleton, ← Finset.coe_insert, ← Finset.coe_insert, ← Finset.coe_insert]
      show d ∈ {d ∈ Finset.range 10 | d ≠ 0 ∧ d % 2 = 0}
      simp
      have bla : (Nat.digits 10 (n + 2)!).find? (· ≠ 0) = .some d := by
        rw [← hn, eq_comm]
        apply Option.some_get!
        rw [List.find?_isSome]
        use (Nat.digits 10 (n + 2)!).getLast
          (by rw [Nat.digits_ne_nil_iff_ne_zero]; exact Nat.factorial_ne_zero (n + 2))
        simp
        exact Nat.getLast_digit_ne_zero 10 (Nat.factorial_ne_zero (n + 2))
      refine ⟨?_, ⟨?_, ?_⟩⟩
      · apply Nat.digits_lt_base (by simp) (show d ∈ Nat.digits 10 (n + 2)! from ?_)
        exact List.mem_of_find?_eq_some bla
      · rw [← ne_eq, ← @decide_eq_true_iff (d ≠ 0)]
        exact @List.find?_some _ (· ≠ 0) _ _ bla
      · rw [← hn]
        apply even_last_non_zero_digit_of_factorization_five_lt_two
          (show (n + 2)! ≠ 0 from Nat.factorial_ne_zero (n + 2))
        exact factorization_factorial_five_lt_two
  · sorry

end Result

end BwM25R1A2
