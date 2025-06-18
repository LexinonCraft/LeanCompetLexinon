import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Archimedean

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

lemma example_seq'_infinite : (setOf ExampleSeqContains).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro n
  use 4 * n + 1
  constructor
  · use 0, n
    simp
  · calc n
    _ ≤ 4 * n := by apply Nat.le_mul_of_pos_left; simp
    _ < _ := by simp

lemma example_seq_not_contains_zero : ¬ ExampleSeqContains 0 := by
  by_contra ha
  obtain ⟨n, m, ha⟩ := ha
  simp at ha

noncomputable def exampleSeq' : ℕ → ℕ := Nat.nth ExampleSeqContains

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

lemma example_seq'_contains (n : ℕ) : ExampleSeqContains (exampleSeq' n) := by
  apply Nat.nth_mem_of_infinite
  exact example_seq'_infinite

lemma example_seq'_pos (n : ℕ) : 0 < exampleSeq' n := by
  apply Nat.zero_lt_of_ne_zero
  by_contra ha
  absurd example_seq_not_contains_zero
  rw [← ha]
  apply example_seq'_contains n

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
  obtain ⟨m₁, l₁, h₁⟩ := example_seq'_contains n₁
  obtain ⟨m₂, l₂, h₂⟩ := example_seq'_contains n₂
  apply example_seq'_inj n₁ n₂
  rw [h₁, h₂] at h ⊢
  cases Nat.le_or_ge m₁ m₂ with
  | inl hm =>
    have hml : m₁ = m₂ ∧ l₁ = l₂ := example_seq_no_sum_two_pow' m₁ l₁ m₂ l₂ k h hm
    rw [hml.left, hml.right]
  | inr hm =>
    rw [add_comm] at h
    have hml : m₂ = m₁ ∧ l₂ = l₁ := example_seq_no_sum_two_pow' m₂ l₂ m₁ l₁ k h hm
    rw [hml.left, hml.right]

lemma lt_card_filter_of_card_filter_not_lt {n k : ℕ} {p : ℕ → Prop} [DecidablePred p]
  (h : k + {m ∈ Finset.range n | ¬ p m}.card < n) : k < {m ∈ Finset.range n | p m}.card := by
  rw [← Nat.lt_sub_iff_add_lt] at h
  conv at h =>
    rhs; left
    rw [← Finset.card_range n]
  rw [← Finset.card_sdiff (by simp), ← Finset.filter_not] at h
  simp at h
  exact h

lemma example_seq_lt (n : ℕ) : exampleSeq' n < 2 * (n + 1) := by
  apply @Nat.nth_lt_of_lt_count _ sorry
  rw [Nat.count_eq_card_filter_range]
  have t : DecidablePred ExampleSeqContains := Classical.decPred ExampleSeqContains
  have h : n + {m ∈ Finset.range (2 * (n + 1)) | ExampleSeqContains m}.card < 2 * (n + 1) := sorry
  --rw [Finset.filter_de]
  --apply @lt_card_filter_of_card_filter_not_lt (2 * (n + 1)) n ExampleSeqContains sorry
  by_contra ha
  simp at ha

  /-
  apply @Nat.nth_lt_of_lt_count _ sorry
  by_contra ha
  simp at ha
  rw [Nat.count_eq_card_filter_range, ← Finset.card_range n] at ha
  -/
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
    · sorry
      --exact example_seq_lt
  · intro h_seq
    obtain ⟨seq, h_seq⟩ := h_seq
    by_contra ha
    apply not_exists_k h_seq
    unfold solution at ha
    simp at ha
    exact exists_k_of_r_lt_two ha h_seq

end Result

end BwM24R2A2
