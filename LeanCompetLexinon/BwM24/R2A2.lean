import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Ring.Parity

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


variable (n n₁ n₂ m l m₁ l₁ m₂ l₂ k : ℕ) {n' : ℕ} {r : ℝ} {seq : ℕ → ℕ}

def decomp : ℕ × ℕ :=
  let m := Nat.findGreatest (2 ^ · ∣ n) n
  let l := (n / 2 ^ m - 1) / 2
  (m, l)

def recomp : ℕ := 2 ^ m * (2 * l + 1)

lemma two_pow_dvd : 2 ^ (decomp n).1 ∣ n :=
  @Nat.findGreatest_spec 0 (2 ^ · ∣ n) _ _ (by simp) (by simp)

lemma two_dvd_div_exp_prime_fac_two_sub_one (hn : n ≠ 0) : 2 ∣ n / 2 ^ (decomp n).1 - 1 := by
  set m := (decomp n).1; apply Nat.dvd_of_mod_eq_zero; apply Nat.sub_mod_eq_zero_of_mod_eq
  rw [← Nat.two_dvd_ne_zero]
  rw [Nat.dvd_div_iff_mul_dvd (two_pow_dvd _), ← Nat.pow_add_one]
  apply @Nat.findGreatest_is_greatest (m + 1) (2 ^ · ∣ n) _ n
  · unfold m; unfold decomp; simp
  · calc
      _ ≤ 2 ^ m := by rw [Nat.add_one_le_iff]; exact Nat.lt_two_pow_self
      _ ≤ n := by refine Nat.le_of_dvd ?_ (two_pow_dvd _); exact Nat.zero_lt_of_ne_zero hn

lemma recomp_decomp (hn : n ≠ 0) : n = 2 ^ (decomp n).1 * (2 * (decomp n).2 + 1) := by
  unfold decomp; simp; set m := Nat.findGreatest (2 ^ · ∣ n) n; rw [show m = (decomp n).1 by rfl]
  rw [Nat.mul_div_cancel' (two_dvd_div_exp_prime_fac_two_sub_one n hn)]
  rw [Nat.sub_one_add_one (by rw [Nat.div_ne_zero_iff_of_dvd (two_pow_dvd _)]; exact ⟨hn, by simp⟩)]
  rw [Nat.mul_div_cancel' (two_pow_dvd _)]

lemma decomp_recomp' : let n := 2 ^ m * (2 * l + 1); Nat.findGreatest (2 ^ · ∣ n) n = m := by
  intro n; rw [eq_comm]; apply eq_of_le_of_not_lt
  · refine Nat.le_findGreatest ?_ (by unfold n; simp)
    calc
      _ ≤ 2 ^ m := by apply le_of_lt; exact Nat.lt_two_pow_self
      _ ≤ 2 ^ m * (2 * l + 1) := by simp
  · generalize hm' : Nat.findGreatest (2 ^ · ∣ n) n = m'; rw [Nat.findGreatest_eq_iff] at hm'
    by_contra ha; have hm' := hm'.right.left; have hm' := hm' (Nat.ne_zero_of_lt ha)
    rw [← Nat.sub_add_cancel ha.le, pow_add, mul_comm] at hm'
    have hm' := Nat.dvd_div_of_mul_dvd hm'; unfold n at hm'; simp at hm'
    absurd (show ¬2 ∣ 2 * l + 1 by simp); refine Nat.dvd_of_pow_dvd ?_ hm'
    rw [Nat.one_le_iff_ne_zero, Nat.ne_zero_iff_zero_lt]; apply Nat.zero_lt_sub_of_lt; exact ha

lemma decomp_recomp : decomp (2 ^ m * (2 * l + 1)) = (m, l) := by
  unfold decomp; rw [decomp_recomp' m l]; simp

def ExampleSeqContains : Prop := n ≠ 0 ∧ 2 ∣ (decomp n).2

instance decidableExampleSeqContains : DecidablePred ExampleSeqContains := by
  intro n; by_cases h : n ≠ 0
  · by_cases h' : 2 ∣ (decomp n).2
    · refine .isTrue ?_; exact ⟨h, h'⟩
    · refine .isFalse ?_; apply not_and_of_not_right; exact h'
  · refine .isFalse ?_; apply not_and_of_not_left; exact h

lemma example_seq_contains_gt : ∃ m ∈ setOf ExampleSeqContains, n < m := by
  use 2 ^ n; refine ⟨?_, Nat.lt_two_pow_self⟩; unfold ExampleSeqContains; simp
  rw [show 2 ^ n = 2 ^ n * (2 * 0 + 1) by simp, decomp_recomp]; simp

lemma example_seq_infinite : (setOf ExampleSeqContains).Infinite := by
  apply Set.infinite_of_forall_exists_gt; exact example_seq_contains_gt

noncomputable def exampleSeq : ℕ → ℕ := Nat.nth ExampleSeqContains

def exampleSeq' : ℕ → List ℕ
| 0 => []
| 1 => [Nat.find (show ∃ n, ExampleSeqContains n by use 1; decide)]
| n + 2 =>
  let xs := exampleSeq' (n + 1)
  match xs.getLast? with
  | some m => xs ++ [Nat.find (example_seq_contains_gt m)]
  | none => []

--#eval exampleSeq' 120

lemma example_seq_contains_mem : ExampleSeqContains (exampleSeq n) := by
  apply Nat.nth_mem_of_infinite; exact example_seq_infinite

lemma example_seq_ne_zero : exampleSeq n ≠ 0 := (example_seq_contains_mem n).left

lemma example_seq_two_dvd_l : 2 ∣ (decomp (exampleSeq n)).2 := (example_seq_contains_mem n).right

lemma example_seq_pos : 0 < exampleSeq n := by
  apply Nat.zero_lt_of_ne_zero; exact example_seq_ne_zero n

lemma example_seq_inj : ∀ n m, exampleSeq n = exampleSeq m → n = m := by
  apply Nat.nth_injective; exact example_seq_infinite

lemma two_dvd_two_pow_sub (h : n₁ < n₂) : 2 ∣ 2 ^ (n₂ - n₁) := by
  show 2 ^ 1 ∣ 2 ^ (n₂ - n₁); rw [Nat.pow_dvd_pow_iff_le_right (show 1 < 2 by simp)]
  rw [Nat.one_le_iff_ne_zero, Nat.ne_zero_iff_zero_lt]; apply Nat.zero_lt_sub_of_lt; exact h

lemma example_seq_m_lt_k (h : recomp m₁ l₁ + recomp m₂ l₂ = 2 ^ k) : m₁ < k := by
  unfold recomp at h; rw [← Nat.pow_lt_pow_iff_right (show 1 < 2 by simp)]
  calc 2 ^ m₁
    _ ≤ 2 ^ m₁ * (2 * l₁ + 1) := by simp
    _ < 2 ^ m₁ * (2 * l₁ + 1)
        + 2 ^ m₂ * (2 * l₂ + 1) := by apply Nat.lt_add_of_pos_right; simp
    _ = 2 ^ k := h

lemma example_seq_m_eq_m_of_sum_pow_two (hm : m₁ < m₂)
    (h : recomp m₁ l₁ + recomp m₂ l₂ = 2 ^ k) : False := by
  have hm₁k : m₁ < k := example_seq_m_lt_k m₁ l₁ m₂ l₂ k h; unfold recomp at h
  rw [← Nat.sub_add_cancel hm.le, ← Nat.sub_add_cancel hm₁k.le, pow_add, pow_add] at h
  conv at h => lhs; right; left; rw [mul_comm];; conv at h => lhs; right; rw [mul_assoc]
  conv at h => rhs; rw [mul_comm];; rw [← Distrib.left_distrib] at h; simp at h
  absurd two_dvd_two_pow_sub m₁ k hm₁k; rw [← h, ← even_iff_two_dvd]; simp
  rw [Nat.odd_add, Nat.even_mul]; simp; rw [even_iff_two_dvd]; exact two_dvd_two_pow_sub m₁ m₂ hm

lemma example_seq_l_eq_l_of_sum_pow_two (hl₁ : 2 ∣ l₁) (hl₂ : 2 ∣ l₂)
    (h : recomp m l₁ + recomp m l₂ = 2 ^ k) : l₁ = l₂ := by
  have hmk : m < k := example_seq_m_lt_k m l₁ m l₂ k h; unfold recomp at h
  rw [← Nat.sub_add_cancel hmk.le, pow_add] at h; conv at h => rhs; rw [mul_comm]
  rw [← Distrib.left_distrib, Nat.add_add_add_comm, ← Distrib.left_distrib] at h; simp at h
  rw [← Nat.sub_one_add_one (show k - m ≠ 0 by rw [Nat.sub_ne_zero_iff_lt]; exact hmk)] at h
  set x := k - m - 1; match x with
  | 0 => simp at h; rw [h.left, h.right]
  | 1 => simp at h; rw [Nat.add_eq_one_iff] at h; cases h with
    | inl h => rw [h.right] at hl₂; simp at hl₂
    | inr h => rw [h.left] at hl₁; simp at hl₁
  | x + 2 =>
    conv at h => lhs; right; rw [show 2 = 2 * 1 by rfl];; rw [← Distrib.left_distrib] at h
    rw [pow_add, mul_comm] at h; simp at h;  absurd show ¬Even (l₁ + l₂ + 1) by
      rw [Nat.even_add_one, Nat.even_add, even_iff_two_dvd, even_iff_two_dvd]; simp
      exact iff_of_true hl₁ hl₂
    rw [h]; rw [show x + 2 = x + 1 + 1 by simp, pow_add, mul_comm]; simp

lemma example_seq_no_sum_two_pow (h : exampleSeq n₁ + exampleSeq n₂ = 2 ^ k) : n₁ = n₂ := by
  apply example_seq_inj
  rw [recomp_decomp (exampleSeq n₁) (example_seq_ne_zero n₁)] at h ⊢
  rw [recomp_decomp (exampleSeq n₂) (example_seq_ne_zero n₂)] at h ⊢
  set m₁ := (decomp (exampleSeq n₁)).1; set l₁ := (decomp (exampleSeq n₁)).2
  set m₂ := (decomp (exampleSeq n₂)).1; set l₂ := (decomp (exampleSeq n₂)).2
  have hm : m₁ = m₂ := by
    by_contra ha; cases lt_or_gt_of_ne ha with
    | inl ha => apply example_seq_m_eq_m_of_sum_pow_two m₁ l₁ m₂ l₂ k ha h
    | inr ha => rw [add_comm] at h; apply example_seq_m_eq_m_of_sum_pow_two m₂ l₂ m₁ l₁ k ha h
  rw [hm] at h ⊢
  have hl : l₁ = l₂ := by
    refine example_seq_l_eq_l_of_sum_pow_two m₂ l₁ l₂ k ?_ ?_ h <;> apply example_seq_two_dvd_l _
  rw [hl]

lemma odd_of_mem
    (n : {k // k ∈ {k ∈ range (exampleSeq n') | 0 ≠ k ∧ ¬ExampleSeqContains k}}) :
    (decomp n.val).2 % 2 = 1 := by
  have h := n.property; rw [mem_filter, ne_comm] at h; unfold ExampleSeqContains at h
  simp at h; apply h.right.right; exact h.right.left

def matchNonMemberWithMember
    (n : {k // k ∈ {k ∈ range (exampleSeq n') | 0 ≠ k ∧ ¬ExampleSeqContains k}}) :
    {k // k ∈ {k ∈ range (exampleSeq n') | 0 ≠ k ∧ ExampleSeqContains k}} := by
  let m := (decomp n).1; let l := (decomp n).2; refine ⟨2 ^ m * (2 * (l - 1) + 1), ?_⟩
  have h := n.property; rw [mem_filter, ne_comm] at h; simp; constructor
  · calc
      _ < n.val := ?_
      _ < exampleSeq n' := ?_
    · rw [recomp_decomp n h.right.left]; unfold m l; by_contra ha; simp at ha
      absurd show ¬ExampleSeqContains n by
        have h' := n.property; rw [mem_filter] at h'; exact h.right.right
      refine ⟨h.right.left, ?_⟩; rw [ha]; simp
    · rw [← mem_range]; exact h.left
  · unfold ExampleSeqContains; simp; rw [decomp_recomp]; simp; rw [Nat.dvd_iff_mod_eq_zero]
    apply Nat.sub_mod_eq_zero_of_mod_eq; unfold l; apply odd_of_mem n

lemma ne_zero_of_mod_ne_zero (h : n % m ≠ 0) : n ≠ 0 := by
  by_contra ha; rw [ha] at h; simp at h

lemma injective_match_non_member_with_member :
  Function.Injective (@matchNonMemberWithMember n') := by
  intros n₁ n₂ h; have hn₁ := n₁.prop; have hn₂ := n₂.prop
  rw [mem_filter, ne_comm] at hn₁ hn₂; unfold matchNonMemberWithMember at h
  simp at h; have h := congr_arg decomp h; rw [decomp_recomp, decomp_recomp] at h; simp at h
  apply Subtype.eq; rw [recomp_decomp n₁ hn₁.right.left, recomp_decomp n₂ hn₂.right.left, ← h.left]
  simp; refine Nat.sub_one_cancel ?_ ?_ h.right <;> rw [← Nat.ne_zero_iff_zero_lt]
  <;> apply ne_zero_of_mod_ne_zero _ 2 <;> rw [Nat.mod_two_ne_zero] <;> exact odd_of_mem _

lemma example_seq_lt (n' : ℕ) : exampleSeq n' < 2 * (n' + 1) := by
  have h : #{n ∈ range (exampleSeq n') | 0 ≠ n ∧ ¬ExampleSeqContains n} ≤
    #{n ∈ range (exampleSeq n') | 0 ≠ n ∧ ExampleSeqContains n} := by
    apply @card_le_card_of_injective _ _ _ _ matchNonMemberWithMember
    exact injective_match_non_member_with_member
  conv at h =>
    rw [← Nat.add_one_le_add_one_iff]
    conv =>
      lhs; rw [filter_and, filter_ne, erase_inter, inter_filter, inter_self]
      rw [card_erase_add_one (by simp; exact ⟨example_seq_pos n', by decide⟩)]
      rw [filter_not, card_sdiff (by simp), card_range]; conv => right; unfold exampleSeq
    conv =>
      rhs; conv =>
        left; args; fun; args; ext n; rw [ne_comm]; unfold ExampleSeqContains
        rw [and_self_left, show n ≠ 0 ∧ 2 ∣ (decomp n).2 ↔ ExampleSeqContains n by rfl]
      unfold exampleSeq
    rw [← Nat.count_eq_card_filter_range, Nat.count_nth_of_infinite example_seq_infinite]
  rw [Distrib.left_distrib, two_mul 1, ← add_assoc, Nat.lt_add_one_iff]
  rw [two_mul, add_assoc, add_comm]; apply Nat.le_add_of_sub_le; exact h

lemma exists_k_of_r_lt_two (hr : r < 2) (h_seq : IsRSeq r seq) :
    ∃ k, ∀ n ≤ 2 ^ k, seq n < 2 ^ (k + 1) := by
  let ⟨k, hk⟩ := exists_nat_gt (2 / (2 - r)); use k; intros n hn; cases hn.lt_or_eq with
  | inl hn =>
    rw [← @Nat.cast_lt ℝ]; calc (seq n : ℝ)
      _ < r * (n + 1 : ℕ) := h_seq.lt n
      _ < 2 * (n + 1 : ℕ) := by
        refine (mul_lt_mul_iff_of_pos_right ?_).mpr hr
        rw [show (0 : ℝ) = (0 : ℕ) by simp, Nat.cast_lt]; simp
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
    rw [hn]; rw [← @Nat.cast_lt ℝ]; calc (seq (2 ^ k) : ℝ)
      _ < r * (2 ^ k + 1 : ℕ) := h_seq.lt (2 ^ k)
      _ < (2 ^ (k + 1) : ℕ) := hk

def mirrorSeq (seq : ℕ → ℕ) (k n : ℕ) : ℕ :=
  let m := seq n; (if m ≤ 2 ^ k then m else 2 ^ (k + 1) - m) - 1

lemma mirror_seq_lt_two_pow_k {r : ℝ} {seq : ℕ → ℕ} (h_seq : IsRSeq r seq) {k n : ℕ} :
    mirrorSeq seq k n < 2 ^ k := by
  unfold mirrorSeq; simp; split_ifs with hn
  · exact Nat.sub_one_lt_of_le (h_seq.pos n) hn
  · rw [← Nat.add_sub_cancel (2 ^ k) (2 ^ k), ← two_mul, ← Nat.pow_add_one', Nat.sub_sub]
    apply Nat.sub_lt_sub_left
    · rw [Nat.pow_add_one']; simp
    · rw [Nat.lt_add_one_iff]; apply Nat.le_of_lt; simp at hn; exact hn

lemma mirror_seq_cancel_one (h_seq : IsRSeq r seq) {k n : ℕ} (h : seq n < 2 ^ (k + 1)) :
    mirrorSeq seq k n + 1 = let m := seq n; if m ≤ 2 ^ k then m else 2 ^ (k + 1) - m := by
  unfold mirrorSeq; simp; apply Nat.sub_one_add_one; rw [Nat.ne_zero_iff_zero_lt]; split_ifs
  · exact h_seq.pos n
  · apply Nat.zero_lt_sub_of_lt
    exact h

lemma lt_pigeon_hole (a b : ℕ) (h₁ : a ≤ b) (h₂ : ∀ c ≤ b, seq c < a) :
    ∃ n ≤ b, ∃ m ≤ b, n ≠ m ∧ seq n = seq m := by
  rw [Nat.le_iff_lt_add_one] at h₁
  let pigeonHoles := range a; let pigeons := range (b + 1)
  let ⟨n, hn, m, hm, n_ne_m, f_n_eq_f_m⟩ : ∃ n ∈ pigeons, ∃ m ∈ pigeons, n ≠ m ∧ seq n = seq m := by
    apply @exists_ne_map_eq_of_card_lt_of_maps_to _ _ _ pigeonHoles
    · rw [card_range, card_range]; exact h₁
    · intros n hn; unfold pigeonHoles; simp; apply h₂; rw [Nat.le_iff_lt_add_one, ← mem_range]
      exact hn
  rw [mem_range, ← Nat.le_iff_lt_add_one] at hn hm; use n; refine ⟨hn, ?_⟩; use m

lemma contra_of_sum_two_pow (h_seq : IsRSeq r seq) {k n m : ℕ}
    (h₁ : seq m < 2 ^ (k + 1)) (h₂ : n ≠ m) (h₃ : seq n = 2 ^ (k + 1) - seq m) : False := by
  absurd h_seq.no_sum_two_pow n m (k + 1); simp; refine ⟨?_, h₂⟩; rw [eq_comm]
  exact Nat.eq_add_of_sub_eq h₁.le h₃.symm

lemma not_exists_k (h_seq : IsRSeq r seq) : ¬ ∃ k, ∀ n ≤ 2 ^ k, seq n < 2 ^ (k + 1) := by
  by_contra ha; obtain ⟨k, hk⟩ := ha; let mSeq := mirrorSeq seq k
  let ⟨n, hn, m, hm, n_ne_m, pair_n_m⟩ : ∃ n ≤ 2 ^ k, ∃ m ≤ 2 ^ k, n ≠ m ∧ mSeq n = mSeq m := by
    apply lt_pigeon_hole (2 ^ k) (2 ^ k) (by simp); intros n _;
    exact mirror_seq_lt_two_pow_k h_seq
  conv at pair_n_m =>
    rw [← Nat.add_one_inj]; unfold mSeq
    rw [mirror_seq_cancel_one h_seq (hk n hn), mirror_seq_cancel_one h_seq (hk m hm)]; simp
  split_ifs at pair_n_m
  · absurd h_seq.inj n m; simp; exact ⟨pair_n_m, n_ne_m⟩
  · exact contra_of_sum_two_pow h_seq (hk m hm) n_ne_m pair_n_m
  · exact contra_of_sum_two_pow h_seq (hk n hn) n_ne_m.symm pair_n_m.symm
  · absurd h_seq.inj n m; conv at pair_n_m =>
      rw [Nat.sub_eq_iff_eq_add (by apply le_of_lt; apply hk; exact hn)]
      rw [← Nat.sub_add_comm (by apply le_of_lt; apply hk; exact hm), Eq.comm]
      rw [Nat.sub_eq_iff_eq_add (by apply Nat.le_add_right_of_le; apply le_of_lt; apply hk; exact hm)]
      simp
    simp; refine ⟨pair_n_m, n_ne_m⟩

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
    · intro n
      calc (exampleSeq n : ℝ)
        _ < (2 * (n + 1) : ℕ) := by rw [Nat.cast_lt]; exact example_seq_lt n
        _ = 2 * (n + 1 : ℕ) := by simp
        _ ≤ r * (n + 1 : ℕ) := ?_
      apply mul_le_mul_of_nonneg_right hr; exact Nat.cast_nonneg (n + 1)
  · intro h_seq; obtain ⟨seq, h_seq⟩ := h_seq; by_contra ha; apply not_exists_k h_seq
    unfold solution at ha; simp at ha; exact exists_k_of_r_lt_two ha h_seq

end Result

end BwM24R2A2
