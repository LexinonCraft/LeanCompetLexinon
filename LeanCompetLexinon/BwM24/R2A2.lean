import Mathlib.Data.Real.Basic

section Problem

structure IsRSeq (r : Real) (seq : Nat → Nat) where
  pos : ∀ n, 0 < seq n
  inj : ∀ m n, m ≠ n → seq m ≠ seq n
  add_ne_two_pow : ¬ ∃ m n k, m ≠ n ∧ seq m + seq n = 2 ^ k
  lt : ∀ n, seq n < (n + 1 : Nat) * r

end Problem

-- ==============================

section Proof

def Nat.destruct (n : Nat) : Nat × Nat :=
  let k := Nat.findGreatest (2 ^ · ∣ n) n
  ⟨k, (n / 2 ^ k - 1) / 2⟩

theorem Nat.two_pow_destruct_fst_dvd_self {n : Nat} : 2 ^ n.destruct.fst ∣ n := by
  unfold destruct
  simp
  apply @Nat.findGreatest_spec 0 (2 ^ · ∣ n) _ n
  · simp
  · simp

theorem Nat.one_le_div_pow_of_ne_zero {n : Nat} : n ≠ 0 → 1 ≤ n / 2 ^ n.destruct.fst := by
  intro n_ne_zero
  rw [one_le_iff_ne_zero]
  refine Nat.div_ne_zero_iff.mpr ⟨?_, ?_⟩
  · simp
  · apply le_of_dvd
    · apply zero_lt_of_ne_zero
      exact n_ne_zero
    · apply @Nat.findGreatest_spec 0 (2 ^ · ∣ n) inferInstance n
      <;> simp

theorem Nat.two_dvd_div_two_pow_destruct_fst_sub_one {n : Nat} :
  n ≠ 0 → 2 ∣ n / 2 ^ n.destruct.fst - 1 := by
  intro n_ne_zero
  rw [← even_iff_two_dvd]
  apply (even_sub' (n.one_le_div_pow_of_ne_zero n_ne_zero)).mpr
  simp
  by_contra h
  simp at h
  rw [even_iff_two_dvd, dvd_div_iff_mul_dvd n.two_pow_destruct_fst_dvd_self] at h
  rw [← Nat.pow_add_one] at h
  absurd h
  apply (Nat.findGreatest_eq_iff.mp (show Nat.findGreatest (2 ^ · ∣ n) n =
    n.destruct.fst by rfl)).right.right
  · simp
  · rw [Nat.add_one_le_iff]
    apply @lt_of_pow_dvd_right 2
    · exact n_ne_zero
    · simp
    · exact two_pow_destruct_fst_dvd_self

theorem Nat.destruct_spec {n : Nat} : n ≠ 0 → let (k, m) := n.destruct;
  n = 2 ^ k * (2 * m + 1) := by
  intro n_ne_zero
  simp
  rw [show n.destruct.snd = (n / 2 ^ n.destruct.fst - 1) / 2 by rfl]
  rw [Nat.mul_div_cancel' (n.two_dvd_div_two_pow_destruct_fst_sub_one n_ne_zero)]
  rw [Nat.sub_add_cancel (n.one_le_div_pow_of_ne_zero n_ne_zero)]
  rw [Nat.mul_div_cancel' n.two_pow_destruct_fst_dvd_self]

structure DestructedNat (n : Nat) where
  k : Nat
  m : Nat
  h : n = 2 ^ k * (2 * m + 1)

def Nat.destructH (n : Nat) (n_ne_zero : n ≠ 0) : DestructedNat n :=
  ⟨n.destruct.fst, n.destruct.snd, n.destruct_spec n_ne_zero⟩

theorem destruct_two_pow_eq : ∀ k, (2 ^ k).destruct = (k, 0) := by
  intro k
  have h : Nat.findGreatest (2 ^ · ∣ 2 ^ k) (2 ^ k) = k := by
    apply Nat.findGreatest_eq_iff.mpr
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · apply le_of_lt
      exact Nat.lt_two_pow_self
    · intro _
      simp
    · intros n hkn _
      apply (Nat.pow_dvd_pow_iff_le_right (by simp)).not.mpr
      exact hkn.not_le
  unfold Nat.destruct
  rw [h]
  simp

def exampleSeqContains (n : Nat) : Bool := 2 ∣ n.destruct.snd

theorem example_seq_infinite : ∀ m, ∃ n > m, exampleSeqContains n := by
  intro m
  use 2 ^ m
  refine .intro Nat.lt_two_pow_self ?_
  unfold exampleSeqContains
  simp
  rw [destruct_two_pow_eq]
  simp

def exampleSeq : Nat → Nat
| 0 => Nat.find (example_seq_infinite 0)
| n + 1 => let prev := exampleSeq n; Nat.find (example_seq_infinite prev)

#eval exampleSeq 10

theorem example_seq_mono : ∀ (m n : Nat), m < n → exampleSeq m < exampleSeq n := by
  intros m n m_lt_n
  induction n with
  | zero =>
    apply False.elim
    apply Nat.not_lt_zero m
    exact m_lt_n
  | succ n' h =>
    have lt_next : exampleSeq n' < exampleSeq (n' + 1) := by
      exact (Nat.find_spec (example_seq_infinite (exampleSeq n'))).left
    refine lt_of_lt_of_le' lt_next ?_
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_add_one m_lt_n) with m_eq_n' | m_lt_n'
    · apply Nat.le_of_eq
      apply congrArg
      exact m_eq_n'
    · apply Nat.le_of_lt
      apply h
      exact m_lt_n'

theorem example_seq_pos : ∀ n, 0 < exampleSeq n := by
  intro n
  by_cases h : n = 0
  · rw [h]
    unfold exampleSeq
    simp
  · apply lt_trans (show 0 < 1 by simp)
    apply example_seq_mono 0 n
    rw [← Nat.ne_zero_iff_zero_lt]
    exact h

theorem two_div_example_seq_mem_snd {n : Nat} : 2 ∣ (exampleSeq n).destruct.snd := by
  rcases n with _ | n'
  · unfold exampleSeq

    --apply Nat.find_spec (example_seq_infinite 0)
    sorry
  · unfold exampleSeq
    --apply (Nat.find_spec (example_seq_infinite n')).right
    sorry

theorem example_seq_mem_scheme (n : Nat) : ∃ k m, exampleSeq n = 2 ^ k * (4 * m + 1) := by
  use (exampleSeq n).destruct.fst, ((exampleSeq n).destruct.snd / 2)
  --rw [show 4 = 2 * 2 by rfl, mul_assoc, Nat.mul_div_cancel']
  sorry

theorem example_seq_add_ne_two_pow_exp_eq (k m m' l : Nat) :
  m ≠ m' → 2 ^ k * (4 * m + 1) + 2 ^ k * (4 * m' + 1) ≠ 2 ^ l := by
  sorry

theorem example_seq_add_ne_two_pow_exp_lt (k k' m m' l : Nat) :
  k < k' → 2 ^ k * (4 * m + 1) + 2 ^ k' * (4 * m' + 1) ≠ 2 ^ l := by
  sorry

theorem example_seq_add_ne_two_pow (n n' l : Nat) :
  n ≠ n' → exampleSeq n + exampleSeq n' ≠ 2 ^ l := by
  intro n_ne_n'
  obtain ⟨k, m, h⟩ := (exampleSeq n).destructH sorry
  obtain ⟨k', m', h'⟩ := (exampleSeq n').destructH sorry
  rw [h, h']


  sorry

end Proof

-- ==============================

section Result

def solution : Set Real := {r | 2 ≤ r}

theorem proof : ∀ r, r ∈ solution ↔ ∃ seq, IsRSeq r seq := by
  intro r
  constructor
  · sorry
  · sorry

end Result
