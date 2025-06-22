import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Card

namespace BwM24R2A2

section Problem

structure IsRSeq (r : ℝ) (seq : ℕ → ℕ) : Prop where
  pos : ∀ n, 0 < seq n
  inj : ∀ n m, seq n = seq m → n = m
  no_sum_two_pow : ∀ n m k, seq n + seq m = 2 ^ k → n = m
  lt : ∀ n, seq n < r * (n + 1 : ℕ)

end Problem

-- ==============================

section Proof

open Finset

def destruct (n : ℕ) : ℕ × ℕ :=
  let m := Nat.findGreatest (2 ^ · ∣ n) n
  let l := (n / 2 ^ m - 1) / 2
  (m, l)

lemma destruct_spec (n : ℕ) (hn : n ≠ 0) : n = 2 ^ (destruct n).1 * (2 * (destruct n).2 + 1) := by
  unfold destruct
  simp
  generalize hm : Nat.findGreatest (2 ^ · ∣ n) n = m
  have dvd_n : 2 ^ m ∣ n := by
    rw [← hm]
    exact @Nat.findGreatest_spec 0 (2 ^ · ∣ n) _ _ (by simp) (by simp)
  have two_dvd : 2 ∣ (n / 2 ^ m - 1) := by
    apply Nat.dvd_of_mod_eq_zero
    apply Nat.sub_mod_eq_zero_of_mod_eq
    rw [← Nat.mod_two_ne_zero]
    rw [ne_eq, ← Nat.dvd_iff_mod_eq_zero, Nat.dvd_div_iff_mul_dvd dvd_n, ← Nat.pow_add_one]
    apply @Nat.findGreatest_is_greatest (m + 1) (2 ^ · ∣ n) _ n
    · rw [hm]
      simp
    · calc m + 1
        _ ≤ 2 ^ m := by rw [Nat.add_one_le_iff]; exact Nat.lt_two_pow_self
      apply Nat.le_of_dvd
      · apply Nat.zero_lt_of_ne_zero
        exact hn
      · exact dvd_n
  have div_ne_zero : n / 2 ^ m ≠ 0 := by
    rw [Nat.div_ne_zero_iff_of_dvd dvd_n]
    exact ⟨hn, by simp⟩
  rw [Nat.mul_div_cancel' two_dvd, Nat.sub_one_add_one div_ne_zero, Nat.mul_div_cancel' dvd_n]

lemma destruct_inj' {m₁ l₁ m₂ l₂ : ℕ} (h : 2 ^ m₁ * (2 * l₁ + 1) = 2 ^ m₂ * (2 * l₂ + 1))
  (hm : m₁ ≤ m₂) : m₁ = m₂ ∧ l₁ = l₂ := by
  conv at h =>
    rw [← Nat.sub_add_cancel hm, pow_add]
    conv =>
      rhs; left
      rw [mul_comm]
    rw [mul_assoc]
    simp
  have dings : m₁ = m₂ := by
    by_contra ha
    have ha := lt_of_le_of_ne hm ha
    absurd show Odd (2 * l₁ + 1) by simp
    rw [h]
    simp
    rw [Nat.even_mul]
    apply Or.inl
    rw [Nat.even_pow]
    simp
    apply Nat.sub_ne_zero_of_lt
    exact ha
  have other_dings : l₁ = l₂ := by
    rw [dings] at h
    simp at h
    exact h
  exact ⟨dings, other_dings⟩

lemma destruct_inj {m₁ l₁ m₂ l₂ : ℕ} (h : 2 ^ m₁ * (2 * l₁ + 1) = 2 ^ m₂ * (2 * l₂ + 1)) :
  m₁ = m₂ ∧ l₁ = l₂ := by
  cases Nat.le_or_ge m₁ m₂ with
  | inl hm =>
    exact destruct_inj' h hm
  | inr hm =>
    rw [eq_comm] at h ⊢
    conv => right; rw [eq_comm]
    exact destruct_inj' h hm

lemma destruct_dings' (m l : ℕ) : let n := 2 ^ m * (2 * l + 1);
  Nat.findGreatest (2 ^ · ∣ n) n = m := by
  apply eq_of_le_of_le
  · generalize hm' : Nat.findGreatest (2 ^ · ∣ 2 ^ m * (2 * l + 1)) (2 ^ m * (2 * l + 1)) = m'
    rw [Nat.findGreatest_eq_iff] at hm'
    by_contra ha
    simp at ha
    absurd show 2 ^ m' ∣ 2 ^ m * (2 * l + 1) by
      apply hm'.right.left
      exact Nat.ne_zero_of_lt ha
    by_contra ha'
    have ⟨q, ha'⟩ := ha'
    rw [← Nat.sub_add_cancel ha.le, pow_add] at ha'
    rw (config := { occs := .pos [4] }) [mul_comm] at ha'
    rw [mul_assoc] at ha'
    simp at ha'
    absurd show Odd (2 * l + 1) by simp
    rw [ha']
    simp
    rw [Nat.even_mul]
    apply Or.inl
    rw [Nat.even_pow]
    refine ⟨by simp, ?_⟩
    rw [Nat.sub_ne_zero_iff_lt]
    exact ha
  · apply Nat.le_findGreatest
    · calc
        _ ≤ 2 ^ m := by apply le_of_lt; exact Nat.lt_two_pow_self
        _ ≤ 2 ^ m * (2 * l + 1) := by simp
    · simp

lemma destruct_dings (m l : ℕ) : destruct (2 ^ m * (2 * l + 1)) = (m, l) := by
  unfold destruct
  rw [destruct_dings' m l]
  simp

lemma destruct_two_pow {m : ℕ} : destruct (2 ^ m) = (m, 0) := by
  rw [show 2 ^ m = 2 ^ m * (2 * 0 + 1) by simp, destruct_dings]

def ExampleSeqContains (n : ℕ) : Prop := n ≠ 0 ∧ 2 ∣ (destruct n).2

instance decidableExampleSeqContains : DecidablePred ExampleSeqContains := by
  intro n
  by_cases h : n ≠ 0
  · by_cases h' : 2 ∣ (destruct n).2
    · refine .isTrue ?_
      exact ⟨h, h'⟩
    · refine .isFalse ?_
      apply not_and_of_not_right
      exact h'
  · refine .isFalse ?_
    apply not_and_of_not_left
    exact h

def ExampleSeqContains' (n : ℕ) : Prop := ∃ m l, n = 2 ^ m * (4 * l + 1)

lemma example_seq'_contains_gt (n : ℕ) : ∃ m ∈ setOf ExampleSeqContains, n < m := by
  use 2 ^ n
  refine ⟨?_, Nat.lt_two_pow_self⟩
  unfold ExampleSeqContains
  simp
  rw [show 2 ^ n = 2 ^ n * (2 * 0 + 1) by simp, destruct_dings]
  simp

lemma example_seq'_infinite : (setOf ExampleSeqContains).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  exact example_seq'_contains_gt

lemma example_seq_not_contains_zero : ¬ ExampleSeqContains 0 := by
  unfold ExampleSeqContains
  simp

noncomputable def exampleSeq' : ℕ → ℕ := Nat.nth ExampleSeqContains

def exampleSeq'' : ℕ → List ℕ
| 0 => []
| 1 => [Nat.find (show ∃ n, ExampleSeqContains n by use 1; decide)]
| n + 2 =>
  let xs := exampleSeq'' (n + 1)
  match xs.getLast? with
  | some m => xs ++ [Nat.find (example_seq'_contains_gt m)]
  | none => []

/-
def exampleSeq'' : ℕ → (List ℕ)
| 0 => []
| n + 1 => by
  let xs := exampleSeq'' n
  refine xs ++ [?_]
  match xs.getLast? with
  | none => exact Nat.find (example_seq_infinite 0)
  | some prev => exact Nat.find (example_seq_infinite (prev + 1))
-/

--#eval exampleSeq' 120

lemma example_seq'_contains (n : ℕ) : ∃ m l, exampleSeq' n = 2 ^ m * (4 * l + 1) := by
  generalize hm : (destruct (exampleSeq' n)).1 = m
  generalize hl : (destruct (exampleSeq' n)).2 = l
  use m, l / 2
  have h : ExampleSeqContains (exampleSeq' n) := by
    apply Nat.nth_mem_of_infinite
    exact example_seq'_infinite
  rw [show 4 = 2 * 2 by rfl, mul_assoc, ← hm, ← hl, Nat.mul_div_cancel' h.right]
  apply destruct_spec
  exact h.left

lemma example_seq'_contains' (n : ℕ) : ExampleSeqContains (exampleSeq' n) := by
  apply Nat.nth_mem_of_infinite
  exact example_seq'_infinite

lemma example_seq'_pos (n : ℕ) : 0 < exampleSeq' n := by
  apply Nat.zero_lt_of_ne_zero
  let ⟨m, l, h⟩ := example_seq'_contains n
  rw [h]
  simp

lemma example_seq'_inj : ∀ n m, exampleSeq' n = exampleSeq' m → n = m := by
  apply Nat.nth_injective
  exact example_seq'_infinite

lemma two_pow_sub_even (n m : ℕ) (h : n < m) : 2 ^ (m - n) = 2 * 2 ^ (m - n - 1) := by
  have h : 0 < m - n := Nat.zero_lt_sub_of_lt h
  rw [← Nat.ne_zero_iff_zero_lt, ← Nat.one_le_iff_ne_zero] at h
  rw [← Nat.pow_add_one', Nat.sub_add_cancel h]

lemma example_seq_no_sum_two_pow' (m₁ l₁ m₂ l₂ k : ℕ)
  (h : 2 ^ m₁ * (4 * l₁ + 1) + 2 ^ m₂ * (4 * l₂ + 1) = 2 ^ k)
  (hm : m₁ ≤ m₂) : m₁ = m₂ ∧ l₁ = l₂ := by
  have h_m₁_lt_k : m₁ < k := by
    rw [← Nat.pow_lt_pow_iff_right (show 1 < 2 by simp)]
    calc 2 ^ m₁
      _ ≤ 2 ^ m₁ * (4 * l₁ + 1) := by simp
      _ < 2 ^ m₁ * (4 * l₁ + 1)
          + 2 ^ m₂ * (4 * l₂ + 1) := by apply Nat.lt_add_of_pos_right; simp
      _ = 2 ^ k := h
  conv at h =>
    lhs; right
    rw [← Nat.sub_add_cancel hm, add_comm, pow_add, mul_assoc]
  conv at h =>
    rhs
    rw [← Nat.sub_add_cancel h_m₁_lt_k.le, add_comm, pow_add]
  rw [← Distrib.left_distrib] at h
  simp at h
  have hm : m₁ = m₂ := by
    by_contra ha
    rw [show ¬ m₁ = m₂ ↔ m₁ ≠ m₂ by rfl, ne_iff_lt_iff_le.mpr hm] at ha
    absurd show Even (2 ^ (k - m₁)) by
      rw [two_pow_sub_even m₁ k h_m₁_lt_k]
      simp
    rw [← h]
    rw [two_pow_sub_even m₁ m₂ ha]
    rw [Nat.even_add, not_iff]
    simp
    rw [show 4 = 2 * 2 by rfl, mul_assoc]
    simp
  have hl : l₁ = l₂ := by
    rw [← hm] at h
    simp at h
    rw [add_add_add_comm, ← Distrib.left_distrib, two_pow_sub_even m₁ k h_m₁_lt_k] at h
    rw [show 4 = 2 * 2 by rfl, mul_assoc, show 1 + 1 = 2 * 1 by rfl] at h
    rw [← Distrib.left_distrib] at h
    simp at h
    generalize h_k_sub_m₁_sub_one : k - m₁ - 1 = x
    rw [h_k_sub_m₁_sub_one] at h
    match x with
    | 0 =>
      simp at h
      rw [h.left, h.right]
    | 1 =>
      simp at h
    | x + 2 =>
      conv at h =>
        rw [pow_add]
        simp
        rhs
        rw [mul_comm, show 4 = 2 * 2 by rfl, mul_assoc]
      absurd show Even (2 * (2 * 2 ^ x)) by simp
      rw [← h]
      simp
  exact ⟨hm, hl⟩

lemma example_seq_no_sum_two_pow (n₁ n₂ k : ℕ) (h : exampleSeq' n₁ + exampleSeq' n₂ = 2 ^ k) :
  n₁ = n₂ := by
  have ⟨m₁, l₁, h₁⟩ := example_seq'_contains n₁
  have ⟨m₂, l₂, h₂⟩ := example_seq'_contains n₂
  apply example_seq'_inj
  rw [h₁, h₂] at h ⊢
  cases Nat.le_or_ge m₁ m₂ with
  | inl hm =>
    have hml : m₁ = m₂ ∧ l₁ = l₂ := example_seq_no_sum_two_pow' m₁ l₁ m₂ l₂ k h hm
    rw [hml.left, hml.right]
  | inr hm =>
    rw [add_comm] at h
    have hml : m₂ = m₁ ∧ l₂ = l₁ := example_seq_no_sum_two_pow' m₂ l₂ m₁ l₁ k h hm
    rw [hml.left, hml.right]

lemma haha {n' : ℕ} (n : {k // k ∈ {k ∈ Finset.range (2 * (n' + 1)) | ¬ExampleSeqContains k}})
  (h : n.val ≠ 0) : (destruct n.val).2 % 2 = 1 := by
  have h' := n.property
  rw [Finset.mem_filter] at h'
  have h' := h'.right
  unfold ExampleSeqContains at h'
  simp at h'
  apply h'
  exact h

def floorToTwoPow (n : ℕ) : ℕ := Nat.findGreatest (2 ^ · ≤ n + 1) n

lemma floor_to_two_pow_spec {n : ℕ} : 2 ^ floorToTwoPow n ≤ n + 1 := by
  apply @Nat.findGreatest_spec 0 (2 ^ · ≤ n + 1)
  · simp
  · simp

/-
lemma floor_to_two_pow_spec₂ {n : ℕ} : n + 1 < 2 ^ (floorToTwoPow n + 1) := by
  rw [lt_iff_not_le]
  apply @Nat.findGreatest_is_greatest (floorToTwoPow n + 1) (2 ^ · ≤ n + 1) _ n
  · apply Nat.lt_add_one
  · sorry
-/

def matchNonMemberNeZeroWithMember {n' : ℕ}
  (n : {k // k ∈ {k ∈ Finset.range (2 * (n' + 1)) | ¬ExampleSeqContains k}}) (h : n.val ≠ 0) :
  {k // k ∈ {k ∈ Finset.range (2 * (n' + 1)) | ExampleSeqContains k}} := by
  let m := (destruct n).1
  let l := (destruct n).2
  refine ⟨2 ^ m * (2 * (l - 1) + 1), ?_⟩
  simp
  constructor
  · calc
      _ < n.val := ?_
      _ < 2 * (n' + 1) := ?_
    · rw [destruct_spec n.val h]
      unfold m l
      by_contra ha
      simp at ha
      absurd show ¬ExampleSeqContains n.val by
        have h' := n.property
        rw [Finset.mem_filter] at h'
        exact h'.right
      refine ⟨h, ?_⟩
      rw [ha]
      simp
    · rw [← Finset.mem_range]
      apply @Finset.mem_of_mem_filter _ (fun k ↦ ¬ExampleSeqContains k) _ _ n.val
      exact n.property
  · unfold ExampleSeqContains
    simp
    rw [destruct_dings]
    simp
    rw [Nat.dvd_iff_mod_eq_zero]
    apply Nat.sub_mod_eq_zero_of_mod_eq
    unfold l
    exact haha n h

def matchNonMemberWithMember {n' : ℕ}
  (n : {k // k ∈ {k ∈ Finset.range (2 * (n' + 1)) | ¬ExampleSeqContains k}}) :
  {k // k ∈ {k ∈ Finset.range (2 * (n' + 1)) | ExampleSeqContains k}} := by
  by_cases h : n.val ≠ 0
  · exact matchNonMemberNeZeroWithMember n h
  · refine ⟨2 ^ floorToTwoPow n', ?_⟩
    simp
    constructor
    · calc
        _ ≤ n' + 1 := floor_to_two_pow_spec
        _ < 2 * (n' + 1) := by simp
    · refine ⟨by simp, ?_⟩
      rw [destruct_two_pow]
      simp

lemma example_seq_lt (n' : ℕ) : exampleSeq' n' < 2 * (n' + 1) := by
  apply Nat.nth_lt_of_lt_count
  rw [Nat.count_eq_card_filter_range, ← Nat.add_one_le_iff]
  rw [← mul_le_mul_left (show 0 < 2 by simp)]
  conv =>
    lhs;
    rw (config := { occs := .pos [1] }) [← Finset.card_range (2 * (n' + 1))]
    rw [← @Finset.filter_card_add_filter_neg_card_eq_card _ _ ExampleSeqContains]
  rw (config := { occs := .pos [3] }) [two_mul]
  simp
  apply Finset.card_le_card_of_injective (show Function.Injective matchNonMemberWithMember from ?_)
  intros n₁ n₂ h
  apply Subtype.eq
  unfold matchNonMemberWithMember matchNonMemberNeZeroWithMember at h
  rw [Subtype.mk.injEq] at h
  have h := congr_arg destruct h
  split_ifs at h with hn₁ hn₂ hn₂
  · rw [destruct_dings, destruct_dings] at h
    simp at h
    rw [destruct_spec n₁.val hn₁, destruct_spec n₂.val hn₂, ← h.left]
    simp
    calc
      _ = (destruct n₁.val).2 - 1 + 1 := (Nat.sub_one_add_one ?_).symm
      _ = (destruct n₂.val).2 - 1 + 1 := by rw [h.right]
      _ = (destruct n₂.val).2 := (Nat.sub_one_add_one ?_)
    · by_contra ha
      absurd haha n₁ hn₁
      rw [ha]
      simp
    · by_contra ha
      absurd haha n₂ hn₂
      rw [ha]
      simp
  · apply False.elim
    absurd show n₁ < 2 * (n' + 1) by
      have h' := n₁.property
      rw [Finset.mem_filter, Finset.mem_range] at h'
      exact h'.left
    simp at h
    rw [destruct_dings, destruct_two_pow] at h
    simp at h
    rw [destruct_spec n₁.val hn₁, h.left]
    sorry
  · sorry
  · simp at hn₁ hn₂
    rw [hn₁, hn₂]
  /-
  conv =>
    rhs; right; left; ext n'
    rw [← @not_not (ExampleSeqContains n')]
  rw [Finset.filter_not, Finset.card_sdiff (by simp)]
  -/
  /-
  rw [Finset.filter_congr _ (ExampleSeqContains ·) (ExampleSeqContains ·) sorry sorry (Finset.range (2 * (n + 1)))]
  conv =>
    rhs; right; congr
    · ext n'
      rw [← @not_not (ExampleSeqContains n')]
    · skip
    · exact sorry
  -/
  --rw [@Finset.filter_not _ (¬ ExampleSeqContains ·) sorry _ (Finset.range (2 * (n + 1)))]
  /-
  have _ : DecidablePred ExampleSeqContains := sorry
  let d := {x ∈ Finset.range (2 * (n + 1)) | ¬ ExampleSeqContains x}
  generalize he : {x ∈ Finset.range (2 * (n + 1)) | ExampleSeqContains x} = e
  -/
  /-
  apply @Nat.nth_lt_of_lt_count _ sorry
  rw [Nat.count_eq_card_filter_range]
  have t : DecidablePred ExampleSeqContains := Classical.decPred ExampleSeqContains
  have h : n + {m ∈ Finset.range (2 * (n + 1)) | ExampleSeqContains m}.card < 2 * (n + 1) := sorry
  -/
  --rw [Finset.filter_de]
  --apply @lt_card_filter_of_card_filter_not_lt (2 * (n + 1)) n ExampleSeqContains sorry
  /-
  apply @Nat.nth_lt_of_lt_count _ sorry
  by_contra ha
  simp at ha
  rw [Nat.count_eq_card_filter_range, ← Finset.card_range n] at ha
  -/
  --sorry

lemma example_seq_lt' (n' : ℕ) : exampleSeq' n' < 2 * (n' + 1) := by
  apply Nat.nth_lt_of_lt_count
  rw [Nat.count_eq_card_filter_range]
  have t : exampleSeq' n' - n' ≤ #{n ∈ Finset.range (exampleSeq' n') | ExampleSeqContains n} := by
    sorry
  have s : n' = #{n ∈ Finset.range (exampleSeq' n') | ExampleSeqContains n} := by
    sorry

  sorry

lemma exists_k_of_r_lt_two {r : ℝ} (hr : r < 2) {seq : ℕ → ℕ} (h_seq : IsRSeq r seq) :
  ∃ k, ∀ n ≤ 2 ^ k, seq n < 2 ^ (k + 1) := by
  let ⟨k, hk⟩ := exists_nat_gt (2 / (2 - r))
  use k
  intros n hn
  cases hn.lt_or_eq with
  | inl hn =>
    rw [← @Nat.cast_lt ℝ]
    calc (seq n : ℝ)
      _ < r * (n + 1 : ℕ) := h_seq.lt n
      _ < 2 * (n + 1 : ℕ) := by
        refine (mul_lt_mul_iff_of_pos_right ?_).mpr hr
        rw [show (0 : ℝ) = (0 : ℕ) by simp, Nat.cast_lt]
        simp
      _ = (2 * (n + 1) : ℕ) := by simp
      _ ≤ (2 ^ (k + 1) : ℕ) := by rw [Nat.cast_le, Nat.pow_add_one']; simp; exact hn.nat_succ_le
  | inr hn =>
    have hk : 2 / (2 - r) < (2 ^ k + 1 : ℕ) := by
      calc 2 / (2 - r)
        _ < (k : ℕ) := hk
        _ < (2 ^ k : ℕ) := by rw [Nat.cast_lt]; exact Nat.lt_two_pow_self
        _ < (2 ^ k + 1 : ℕ) := by rw [Nat.cast_lt]; simp
    conv at hk =>
      rw [div_lt_iff₀ (by rw [sub_pos]; exact hr), sub_eq_add_neg, Distrib.left_distrib]
      rw [show (2 : ℝ) = (2 : ℕ) by simp, ← Nat.cast_mul, Distrib.right_distrib]
      rw [← Nat.pow_add_one, mul_neg, ← sub_eq_add_neg, lt_sub_iff_add_lt]
      rw [add_comm, ← lt_sub_iff_add_lt, ← Nat.cast_sub (by simp), mul_comm]
    rw [hn]
    rw [← @Nat.cast_lt ℝ]
    calc (seq (2 ^ k) : ℝ)
      _ < r * (2 ^ k + 1 : ℕ) := h_seq.lt (2 ^ k)
      _ < (2 ^ (k + 1) : ℕ) := hk

def mirrorSeq (seq : ℕ → ℕ) (k n : ℕ) : ℕ :=
  let m := seq n; (if m ≤ 2 ^ k then m else 2 ^ (k + 1) - m) - 1

lemma mirror_seq_lt_two_pow_k {r : ℝ} {seq : ℕ → ℕ} (h_seq : IsRSeq r seq) {k n : ℕ} :
  mirrorSeq seq k n < 2 ^ k := by
  unfold mirrorSeq
  simp
  split_ifs with hn
  · apply Nat.sub_one_lt_of_le
    · exact h_seq.pos n
    · exact hn
  · rw [← Nat.add_sub_cancel (2 ^ k) (2 ^ k), ← two_mul, ← Nat.pow_add_one', Nat.sub_sub]
    apply Nat.sub_lt_sub_left
    · rw [Nat.pow_add_one']
      simp
    · rw [Nat.lt_add_one_iff]
      apply Nat.le_of_lt
      simp at hn
      exact hn

lemma mirror_seq_cancel_one {r : ℝ} {seq : ℕ → ℕ} (h_seq : IsRSeq r seq) {k n : ℕ}
  (h : seq n < 2 ^ (k + 1)) :
  mirrorSeq seq k n + 1 = let m := seq n; if m ≤ 2 ^ k then m else 2 ^ (k + 1) - m := by
  unfold mirrorSeq
  simp
  apply Nat.sub_one_add_one
  rw [Nat.ne_zero_iff_zero_lt]
  split_ifs
  · exact h_seq.pos n
  · apply Nat.zero_lt_sub_of_lt
    exact h

lemma lt_pigeon_hole (a b : ℕ) (f : ℕ → ℕ) (h₁ : a ≤ b) (h₂ : ∀ c ≤ b, f c < a) :
  ∃ n ≤ b, ∃ m ≤ b, n ≠ m ∧ f n = f m := by
  rw [Nat.le_iff_lt_add_one] at h₁
  let pigeonHoles := Finset.range a
  let pigeons := Finset.range (b + 1)
  let ⟨n, hn, m, hm, n_ne_m, f_n_eq_f_m⟩ : ∃ n ∈ pigeons, ∃ m ∈ pigeons, n ≠ m ∧ f n = f m := by
    apply @Finset.exists_ne_map_eq_of_card_lt_of_maps_to _ _ _ pigeonHoles
    · rw [Finset.card_range, Finset.card_range]
      exact h₁
    · intros n hn
      rw [Finset.mem_range]
      apply h₂
      rw [Nat.le_iff_lt_add_one, ← Finset.mem_range]
      exact hn
  rw [Finset.mem_range, ← Nat.le_iff_lt_add_one] at hn hm
  use n
  refine ⟨hn, ?_⟩
  use m

lemma contra_of_sum_two_pow {r : ℝ} {seq : ℕ → ℕ} (h_seq : IsRSeq r seq) {k n m : ℕ}
  (h₁ : seq m < 2 ^ (k + 1)) (h₂ : n ≠ m) (h₃ : seq n = 2 ^ (k + 1) - seq m) : False := by
  absurd h_seq.no_sum_two_pow n m (k + 1)
  simp
  refine ⟨?_, h₂⟩
  symm
  apply Nat.eq_add_of_sub_eq
  · exact h₁.le
  · exact h₃.symm

lemma not_exists_k {r : ℝ} {seq : ℕ → ℕ} (h_seq : IsRSeq r seq) :
  ¬ ∃ k, ∀ n ≤ 2 ^ k, seq n < 2 ^ (k + 1) := by
  by_contra ha
  obtain ⟨k, hk⟩ := ha
  let mSeq := mirrorSeq seq k
  let ⟨n, hn, m, hm, n_ne_m, pair_n_m⟩ : ∃ n ≤ 2 ^ k, ∃ m ≤ 2 ^ k, n ≠ m ∧ mSeq n = mSeq m := by
    apply lt_pigeon_hole (2 ^ k) (2 ^ k) mSeq
    · simp
    · intros n _
      exact mirror_seq_lt_two_pow_k h_seq
  conv at pair_n_m =>
    rw [← Nat.add_one_inj]
    unfold mSeq
    rw [mirror_seq_cancel_one h_seq (hk n hn), mirror_seq_cancel_one h_seq (hk m hm)]
    simp
  split_ifs at pair_n_m
  · absurd h_seq.inj n m
    simp
    exact ⟨pair_n_m, n_ne_m⟩
  · exact contra_of_sum_two_pow h_seq (hk m hm) n_ne_m pair_n_m
  · exact contra_of_sum_two_pow h_seq (hk n hn) n_ne_m.symm pair_n_m.symm
  · absurd h_seq.inj n m
    conv at pair_n_m =>
      rw [Nat.sub_eq_iff_eq_add (by apply le_of_lt; apply hk; exact hn)]
      rw [← Nat.sub_add_comm (by apply le_of_lt; apply hk; exact hm)]
      rw [Eq.comm]
      rw [Nat.sub_eq_iff_eq_add (by apply Nat.le_add_right_of_le; apply le_of_lt; apply hk; exact hm)]
      simp
    simp
    refine ⟨pair_n_m, n_ne_m⟩

end Proof

-- ==============================

section Result

def solution : Set ℝ := {r | 2 ≤ r}

theorem proof : ∀ r, r ∈ solution ↔ ∃ seq, IsRSeq r seq := by
  intro r
  constructor
  · intro hr
    use exampleSeq'
    constructor
    · exact example_seq'_pos
    · exact example_seq'_inj
    · exact example_seq_no_sum_two_pow
    · intro n
      calc (exampleSeq' n : ℝ)
        _ < (2 * (n + 1) : ℕ) := by rw [Nat.cast_lt]; exact example_seq_lt n
        _ = 2 * (n + 1 : ℕ) := by simp
        _ ≤ r * (n + 1 : ℕ) := ?_
      apply mul_le_mul_of_nonneg_right hr
      exact Nat.cast_nonneg (n + 1)
  · intro h_seq
    obtain ⟨seq, h_seq⟩ := h_seq
    by_contra ha
    apply not_exists_k h_seq
    unfold solution at ha
    simp at ha
    exact exists_k_of_r_lt_two ha h_seq

end Result

end BwM24R2A2
