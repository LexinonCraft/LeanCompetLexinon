import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card

section Problem

structure IsRSeq (r : Real) (seq : Nat → Nat) where
  pos : ∀ n, 0 < seq n
  inj : ∀ m n, m ≠ n → seq m ≠ seq n
  add_ne_two_pow : ¬ ∃ m n k, m ≠ n ∧ seq m + seq n = 2 ^ k
  lt : ∀ n, seq n < (n + 1 : Nat) * r

end Problem

-- ==============================

section Proof

inductive ExampleSeqContains : Nat → Prop where
| half (n : Nat) : ExampleSeqContains n → ExampleSeqContains (2 * n)
| mod (n : Nat) : ExampleSeqContains (4 * n + 1)

instance decExampleSeqContains : DecidablePred (ExampleSeqContains ·) := by
  apply Nat.strongRec
  intros n f
  simp
  by_cases n_zero : n = 0
  · refine .isFalse ?_
    by_contra h₁
    induction h₁ with
    | half n' _ h₂ =>
      absurd n_zero
      simp
      --exact h₂
      sorry
    | mod n' =>
      absurd n_zero
      simp
  sorry

def exampleSeqContains : Nat → Bool := by
  apply Nat.strongRec
  intros n f
  by_cases n_zero : n = 0
  · exact false
  by_cases n_even : n % 2 = 0
  · apply f (n / 2)
    apply Nat.div_lt_self
    · exact Nat.zero_lt_of_ne_zero n_zero
    · simp
  exact Decidable.decide (n % 4 = 1)

lemma example_seq_not_empty : ∃ n, exampleSeqContains n := by
  use 1
  unfold exampleSeqContains
  unfold Nat.strongRec
  rfl

lemma example_seq_unbound (m : Nat) : ∃ n > m, exampleSeqContains n := by
  use 2 ^ m
  refine ⟨Nat.lt_two_pow_self, ?_⟩
  unfold exampleSeqContains
  induction m with
  | zero =>
    unfold Nat.strongRec
    simp
  | succ m' h =>
    unfold Nat.strongRec
    simp
    simp at h
    rw [Nat.pow_add_one, Nat.mul_div_cancel (2 ^ m') (by simp), h]

def exampleSeq : Nat → Nat
| 0 => Nat.find example_seq_not_empty
| n + 1 => let prev := exampleSeq n; Nat.find (example_seq_unbound prev)

#eval exampleSeq 0

lemma example_seq_contains (n : Nat) : exampleSeqContains (exampleSeq n) := by
  cases n with
  | zero =>
    exact @Nat.find_spec (exampleSeqContains · = true) _ _
  | succ n' =>
    exact (@Nat.find_spec (fun m => m > exampleSeq n' ∧ exampleSeqContains m = true) _ _).right

lemma example_seq_mono : ∀ (m n : Nat), m < n → exampleSeq m < exampleSeq n := by
  intro m n m_lt_n
  induction n with
  | zero =>
    apply False.elim
    apply Nat.not_lt_zero m
    exact m_lt_n
  | succ n' h =>
    have lt_next : exampleSeq n' < exampleSeq (n' + 1) := by
      exact (Nat.find_spec (example_seq_unbound (exampleSeq n'))).left
    refine lt_of_lt_of_le' lt_next ?_
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_add_one m_lt_n) with m_eq_n' | m_lt_n'
    · apply Nat.le_of_eq
      apply congrArg
      exact m_eq_n'
    · apply Nat.le_of_lt
      apply h
      exact m_lt_n'

theorem example_seq_pos : ∀ n : Nat, 0 < exampleSeq n := by
  intro n
  apply Nat.zero_lt_of_ne_zero
  by_contra h
  absurd example_seq_contains n
  rw [h]
  unfold exampleSeqContains
  unfold Nat.strongRec
  simp

theorem example_seq_inj : ∀ m n, m ≠ n → exampleSeq m ≠ exampleSeq n := by
  intros m n m_ne_n
  rcases lt_or_gt_of_ne m_ne_n with m_lt_n | m_gt_n
  · apply ne_of_lt
    apply example_seq_mono
    exact m_lt_n
  · apply ne_of_gt
    apply example_seq_mono
    exact m_gt_n

lemma example_seq_contains_add_ne_two_pow (m n k : Nat) (hm : exampleSeqContains m)
  (hn : exampleSeqContains n) (h : m + n = 2 ^ k) : m = n := by

  sorry

theorem example_seq_add_ne_two_pow : ∀ m n k, m ≠ n → exampleSeq m + exampleSeq n ≠ 2 ^ k := by
  intros m n k h₁
  by_contra h₂
  absurd example_seq_inj m n h₁
  apply example_seq_contains_add_ne_two_pow (exampleSeq m) (exampleSeq n) k
  · exact example_seq_contains m
  · exact example_seq_contains n
  · exact h₂

theorem seq_init_lt_of_r_lt_two {r : Real} (hr : r < 2) {seq : Nat → Nat} (hseq : IsRSeq r seq) :
  ∃ m, ∀ n ≤ 2 ^ m, seq n < 2 ^ m * 2 := by
  let ⟨m, hm⟩ := exists_nat_gt (2 * (2 - r)⁻¹)
  have h_two_pow_m : 2 * (2 - r)⁻¹ < (2 ^ m + 1 : Nat) := by
      trans (m : Real)
      · exact hm
      · apply Nat.cast_lt.mpr
        apply Nat.lt_add_one_of_lt
        exact Nat.lt_two_pow_self
  conv at h_two_pow_m =>
    rw [← lt_mul_inv_iff₀ (show 0 < (2 - r)⁻¹ by apply inv_pos.mpr; apply sub_pos.mpr; exact hr)]
    rw [inv_inv, sub_eq_add_neg, Distrib.left_distrib, mul_neg, ← sub_eq_add_neg]
    rw [lt_sub_iff_add_lt, add_comm, ← lt_sub_iff_add_lt]
    rw [show ((2 ^ m + 1 : Nat) * 2 - 2 : Real) = ((2 ^ m + 1) * 2 - 2 : Nat) by simp]
    rw [Distrib.right_distrib, one_mul, Nat.add_sub_cancel]
  use m
  intros n hn
  rcases hn.lt_or_eq with hn' | hn'
  · rw [show seq n < 2 ^ m * 2 ↔ (seq n : Real) < (2 ^ m * 2 : Nat) from Nat.cast_lt.symm]
    trans (n + 1 : Nat) * r
    · exact hseq.lt n
    · refine lt_of_le_of_lt' ?_ (show (n + 1 : Nat) * r < ((n + 1) * 2 : Nat) from ?_)
      · rw [Nat.cast_le]
        apply Nat.mul_le_mul_right 2
        exact hn'.nat_succ_le
      · rw [Nat.cast_mul, mul_lt_mul_iff_of_pos_left (by rw [Nat.cast_pos]; simp)]
        exact hr
  · refine Nat.cast_lt.mp (show (seq n : Real) < (2 ^ m * 2 : Nat) from ?_)
    rw [hn']
    trans (2 ^ m + 1 : Nat) * r
    · exact hseq.lt (2 ^ m)
    · exact h_two_pow_m

def flipSeq (seq : Nat → Nat) (m n : Nat) : Nat := let s := seq n
  (if (s.decLe (2 ^ m)).decide then s else 2 ^ m * 2 - s) - 1

lemma flip_seq_spec_le {seq : Nat → Nat} {m n : Nat} (h : seq n ≤ 2 ^ m) :
  flipSeq seq m n = seq n - 1 := by
  unfold flipSeq
  simp [-decide_eq_true_eq]
  rw [decide_eq_true h]
  simp

lemma flip_seq_spec_gt {seq : Nat → Nat} {m n : Nat} (h : ¬ (seq n ≤ 2 ^ m)) :
  flipSeq seq m n = 2 ^ m * 2 - seq n - 1 := by
  unfold flipSeq
  simp [-decide_eq_true_eq]
  rw [decide_eq_false h]
  simp

lemma flip_seq_lt {seq : Nat → Nat} {m n : Nat} : flipSeq seq m n < 2 ^ m := by
  by_cases h : seq n ≤ 2 ^ m
  · rw [flip_seq_spec_le h]
    refine lt_of_le_of_lt ?_ (show 2 ^ m - 1 < 2 ^ m from ?_)
    · apply Nat.sub_le_sub_right
      exact h
    · simp
  · rw [flip_seq_spec_gt h, Nat.sub_sub]
    simp at h
    by_cases h' : seq n + 1 ≤ 2 ^ m * 2
    · rw [Nat.sub_lt_iff_lt_add h', mul_two, add_lt_add_iff_right]
      apply Nat.lt_add_one_of_lt
      exact h
    · simp at h'
      rw [Nat.sub_eq_zero_iff_le.mpr h'.le]
      simp

lemma exist_two_mems (seq : Nat → Nat) (m : Nat) :
  ∃ n n', n ≠ n' ∧ n ≤ 2 ^ m ∧ n' ≤ 2 ^ m ∧ flipSeq seq m n = flipSeq seq m n' := by
  let pigeons := Finset.range (2 ^ m + 1)
  let pigeonHoles := Finset.range (2 ^ m)
  have h' : ∃ n ∈ pigeons, ∃ n' ∈ pigeons,
    n ≠ n' ∧ flipSeq seq m n = flipSeq seq m n' := by
    refine Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (show pigeonHoles.card < pigeons.card from ?_) ?_
    · rw [Finset.card_range, Finset.card_range]
      simp
    · intros n _
      rw [Finset.mem_range]
      exact flip_seq_lt
  let ⟨n, ⟨hn, ⟨n', ⟨hn', ⟨hnn', hfs⟩⟩⟩⟩⟩ := h'
  use n, n'
  refine ⟨hnn', ⟨?_, ⟨?_, hfs⟩⟩⟩
  <;> rw [← Nat.lt_add_one_iff, ← Finset.mem_range]
  · exact hn
  · exact hn'

theorem not_seq_init_lt {r : Real} {seq : Nat → Nat} (hseq : IsRSeq r seq) :
  ¬ ∃ m, ∀ n ≤ 2 ^ m, seq n < 2 ^ m * 2 := by
  by_contra h
  let ⟨m, hm⟩ := h
  let ⟨n, n', ⟨hnn', ⟨hn, ⟨hn', hfs⟩⟩⟩⟩ := exist_two_mems seq m
  by_cases hsn : seq n ≤ 2 ^ m
  · by_cases hsn' : seq n' ≤ 2 ^ m
    · absurd hseq.inj n n' hnn'
      rw [flip_seq_spec_le hsn, flip_seq_spec_le hsn'] at hfs
      apply Nat.sub_one_cancel
      · exact hseq.pos n
      · exact hseq.pos n'
      · exact hfs
    · absurd hseq.add_ne_two_pow
      use n, n', m + 1
      refine ⟨hnn', ?_⟩
      rw [flip_seq_spec_le hsn, flip_seq_spec_gt hsn'] at hfs
      apply Nat.sub_one_cancel
      ·
        sorry
      · sorry
      · sorry
  · by_cases hsn' : seq n' ≤ 2 ^ m
    ·
      sorry
    · absurd hseq.inj n n' hnn'
      rw [flip_seq_spec_gt hsn, flip_seq_spec_gt hsn'] at hfs
      rw [Nat.sub_sub, Nat.sub_sub] at hfs

      sorry

end Proof

-- ==============================

section Result

def answer : Set Real := {r | 2 ≤ r}

theorem proof : ∀ r, r ∈ answer ↔ ∃ seq, IsRSeq r seq := by
  intro r
  constructor
  · sorry
  · intro exists_seq
    have ⟨seq, hseq⟩ := exists_seq
    unfold answer
    simp
    by_contra hr
    rw [← lt_iff_not_le] at hr
    absurd seq_init_lt_of_r_lt_two hr hseq
    exact not_seq_init_lt hseq

end Result
