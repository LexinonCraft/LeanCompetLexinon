import Mathlib.Data.Real.Basic

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

def ExampleSeqContains (n : ℕ) : Prop := ∃ m l, n = 2 ^ m * (4 * l + 1)

lemma example_seq_infinite (n : ℕ) : ∃ m, n ≤ m ∧ ExampleSeqContains m := by
  use 4 * n + 1
  constructor
  · trans 4 * n
    · apply Nat.le_mul_of_pos_left
      simp
    · simp
  · use 0, n
    simp

lemma example_seq_not_contains_zero : ¬ ExampleSeqContains 0 := by
  by_contra ha
  obtain ⟨n, m, ha⟩ := ha
  simp at ha

instance decidableExampleSeqContains (n : ℕ) : Decidable (ExampleSeqContains n) := by
  induction n using Nat.strongRec with
  | ind n decInd =>
    cases Nat.decEq n 0 with
    | isTrue h_n_eq_zero =>
      refine .isFalse ?_
      rw [h_n_eq_zero]
      exact example_seq_not_contains_zero
    | isFalse h_n_ne_zero =>
      cases Nat.decEq (n % 2) 0 with
      | isTrue h_n_even =>
        cases decInd (n / 2) (by exact Nat.bitwise_rec_lemma h_n_ne_zero) with
        | isTrue h_ind =>
          refine .isTrue ?_
          rw [← Nat.div_add_mod n 2, h_n_even]
          simp
          sorry
        | isFalse h_ind =>
          refine .isFalse ?_
          by_contra ha
          sorry
      | isFalse h_n_odd =>
        cases Nat.decEq (n % 4) 1 with
        | isTrue h_n_mod_four_eq_one =>
          refine .isTrue ?_
          rw [← Nat.div_add_mod n 4, h_n_mod_four_eq_one]
          use 0, n / 4
          simp
        | isFalse h_n_mod_four_ne_one =>
          refine .isFalse ?_
          by_contra ha
          obtain ⟨m, l, ha⟩ := ha
          sorry

/-
instance decidableExampleSeqContains (n : ℕ) : Decidable (ExampleSeqContains n) := by
  induction n using Nat.strongRec with
  | ind n decInd =>
    cases Nat.decEq n 0 with
    | isTrue h_n_eq_zero =>
      refine .isFalse ?_
      rw [h_n_eq_zero]
      exact example_seq_not_contains_zero
    | isFalse h_n_ne_zero =>
      cases Nat.decEq (n % 2) 0 with
      | isTrue h_n_even =>
        cases decInd (n / 2) (by exact Nat.bitwise_rec_lemma h_n_ne_zero) with
        | isTrue h_ind =>
          refine .isTrue ?_
          rw [← Nat.div_add_mod n 2, h_n_even]
          simp
          exact .double (n / 2) h_ind
        | isFalse h_ind =>
          refine .isFalse ?_
          by_contra ha
          cases ha with
          | double n ha =>
            rw [mul_comm, Nat.mul_div_cancel n (by simp)] at h_ind
            absurd h_ind
            exact ha
          | mod n =>
            rw [← Nat.mod_add_mod, show 4 = 2 * 2 by rfl, mul_assoc] at h_n_even
            simp at h_n_even
      | isFalse h_n_odd =>
        cases Nat.decEq (n % 4) 1 with
        | isTrue h_n_mod_four_eq_one =>
          refine .isTrue ?_
          rw [← Nat.div_add_mod n 4, h_n_mod_four_eq_one]
          exact .mod _
        | isFalse h_n_mod_four_ne_one =>
          refine .isFalse ?_
          by_contra ha
          cases ha with
          | double n ha =>
            simp at h_n_odd
          | mod n =>
            simp at h_n_mod_four_ne_one
-/

def exampleSeq (n : ℕ) : ℕ :=
  let prev_add_one_or_zero := match n with
  | 0 => 0
  | n + 1 => exampleSeq n + 1
  Nat.find (example_seq_infinite prev_add_one_or_zero)

def exampleSeq' : ℕ → (List ℕ)
| 0 => []
| n + 1 => by
  let xs := exampleSeq' n
  refine xs ++ [?_]
  match xs.getLast? with
  | none => exact Nat.find (example_seq_infinite 0)
  | some prev => exact Nat.find (example_seq_infinite (prev + 1))

--#eval exampleSeq' 120

lemma example_seq_contains (n : ℕ) : ExampleSeqContains (exampleSeq n) := by
  let prev_add_one_or_zero := match n with
  | 0 => 0
  | m + 1 => exampleSeq m + 1
  have h' := Nat.find_spec (example_seq_infinite prev_add_one_or_zero)
  unfold exampleSeq
  simp
  exact h'.right

lemma example_seq_pos (n : ℕ) : 0 < exampleSeq n := by
  apply Nat.zero_lt_of_ne_zero
  by_contra ha
  absurd example_seq_not_contains_zero
  rw [← ha]
  apply example_seq_contains n

lemma example_seq_mono' (n : ℕ) : exampleSeq n < exampleSeq (n + 1) := by
  rw [← add_lt_add_iff_right 1, ← Nat.le_iff_lt_add_one]
  conv =>
    rhs
    unfold exampleSeq
    simp
  have h := Nat.find_spec (example_seq_infinite (exampleSeq n + 1))
  exact h.left

lemma example_seq_mono (n m : ℕ) (h : n < m) : exampleSeq n < exampleSeq m := by
  induction m with
  | zero =>
    simp at h
  | succ m h' =>
    rw [← Nat.le_iff_lt_add_one] at h
    cases eq_or_lt_of_le h with
    | inl h =>
      rw [← h]
      exact example_seq_mono' n
    | inr h =>
      trans exampleSeq m
      · apply h'
        exact h
      · exact example_seq_mono' m

lemma example_seq_inj (n m : ℕ) (h : exampleSeq n = exampleSeq m) : n = m := by
  by_contra ha
  absurd h
  cases lt_or_gt_of_ne ha with
  | inl ha =>
    apply ne_of_lt
    apply example_seq_mono
    exact ha
  | inr ha =>
    apply ne_of_gt
    apply example_seq_mono
    exact ha

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

lemma example_seq_no_sum_two_pow (n₁ n₂ k : ℕ) (h : exampleSeq n₁ + exampleSeq n₂ = 2 ^ k) :
  n₁ = n₂ := by
  obtain ⟨m₁, l₁, h₁⟩ := example_seq_contains n₁
  obtain ⟨m₂, l₂, h₂⟩ := example_seq_contains n₂
  apply example_seq_inj n₁ n₂
  rw [h₁, h₂] at h ⊢
  cases Nat.le_or_ge m₁ m₂ with
  | inl hm =>
    have hml : m₁ = m₂ ∧ l₁ = l₂ := example_seq_no_sum_two_pow' m₁ l₁ m₂ l₂ k h hm
    rw [hml.left, hml.right]
  | inr hm =>
    rw [add_comm] at h
    have hml : m₂ = m₁ ∧ l₂ = l₁ := example_seq_no_sum_two_pow' m₂ l₂ m₁ l₁ k h hm
    rw [hml.left, hml.right]

end Proof

-- ==============================

section Result

def solution : Set ℝ := {r | 2 ≤ r}

theorem proof : ∀ r, r ∈ solution ↔ ∃ seq, IsRSeq r seq := by
  intro r
  constructor
  · intro hr
    use exampleSeq
    constructor
    · exact example_seq_pos
    · exact example_seq_inj
    · exact example_seq_no_sum_two_pow
    · sorry
  · sorry

end Result

end BwM24R2A2
