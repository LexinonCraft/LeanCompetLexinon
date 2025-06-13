import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Factors
import Mathlib.Order.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Archimedean

section Problem

structure IsRSeq (r : Real) (seq : Nat → Nat) where
  pos : ∀ n, 0 < seq n
  inj : ∀ m n, m ≠ n → seq m ≠ seq n
  add_ne_two_pow : ¬ ∃ m n k, m ≠ n ∧ seq m + seq n = 2 ^ k
  lt : ∀ n, seq n < (n + 1 : Nat) * r

end Problem

-- ==============================

section Proof

def exampleSeqSet : Set Nat := {n | ∃ k m : Nat, n = (2 ^ k) * (4 * m + 1)}

theorem example_seq_set_infinite : ∀ n, ∃ m, n < m ∧ m ∈ exampleSeqSet := by
  intro n
  use 2 ^ n
  constructor
  · apply Nat.lt_pow_self
    simp
  · unfold exampleSeqSet
    simp
    use n, 0
    simp

instance instDecidableMemberExampleSeqSet (n : Nat) : Decidable (n ∈ exampleSeqSet) := by
  by_cases h0 : n = 0
  · rw [h0]
    refine .isFalse ?_
    by_contra ha
    unfold exampleSeqSet at ha
    simp at ha
  · let k := Nat.findGreatest (fun k' => 2 ^ k' ∣ n) n
    have hk : 2 ^ k ∣ n := by
      refine @Nat.findGreatest_spec 0 (fun m => 2 ^ m ∣ n)
        inferInstance n (Nat.zero_le n) (show 2 ^ 0 ∣ n from ?_)
      exact Nat.one_dvd n
    let l := n / (2 ^ k)
    by_cases hm4 : l % 4 = 1
    · refine .isTrue ?_
      unfold exampleSeqSet
      simp
      use k, (l - 1) / 4
      refine (Nat.div_eq_iff_eq_mul_right ?_ hk).mp ?_
      · simp
      · rw [← hm4]
        rw [← Nat.div_eq_sub_mod_div]
        rw [Nat.div_add_mod]
    · refine .isFalse ?_
      by_contra ha
      unfold exampleSeqSet at ha
      simp at ha
      obtain ⟨k', m, ha⟩ := ha
      rcases k.lt_trichotomy k' with hkk' | hkk' | hkk'
      · absurd hkk'
        simp
        refine Nat.le_findGreatest ?_ ⟨4 * m + 1, ha⟩
        trans 2 ^ k'
        · apply Nat.le_of_lt
          exact Nat.lt_two_pow_self
        · rw [ha]
          simp
      · rw [← hkk'] at ha
        obtain ha := Nat.div_eq_of_eq_mul_right (by simp) ha
        rw [show n / (2 ^ k) = l by rfl] at ha
        rw [ha] at hm4
        apply hm4
        simp
      · rw [show n = (2 ^ k) * l by symm; exact Nat.mul_div_cancel' hk] at ha
        rw [← Nat.pow_sub_mul_pow 2 (show k' ≤ k from Nat.le_of_lt hkk')] at ha
        conv at ha =>
          lhs
          left
          rw [Nat.mul_comm]
        rw [Nat.mul_assoc] at ha
        obtain ha := Nat.mul_left_cancel (by simp) ha
        absurd show Even (2 ^ (k - k') * l) from ?_
        · apply Nat.even_mul.mpr
          left
          refine (Nat.even_pow' ?_).mpr ?_
          · exact Nat.sub_ne_zero_of_lt hkk'
          · simp
        · rw [ha]
          rw [show 4 = 2 * 2 by simp]
          rw [Nat.mul_assoc]
          simp

instance instDecidableNextNumber (n : Nat) : DecidablePred (fun m => n < m ∧ m ∈ exampleSeqSet) := by
  intro m
  cases d : Decidable.decide (n < m)
  · refine .isFalse ?_
    by_contra
    apply of_decide_eq_false d
    apply And.left
    assumption
  · cases d' : Decidable.decide (m ∈ exampleSeqSet)
    · refine .isFalse ?_
      by_contra
      apply of_decide_eq_false d'
      apply And.right
      assumption
    · refine .isTrue ?_
      exact ⟨of_decide_eq_true d, of_decide_eq_true d'⟩

def exampleSeq : Nat → Nat
| 0 => Nat.find (example_seq_set_infinite 0)
| n + 1 => Nat.find (example_seq_set_infinite (exampleSeq n))

#eval exampleSeq 100

theorem example_seq_mem : ∀ n, exampleSeq n ∈ exampleSeqSet := by
  intro n
  rcases n with _ | n
  · exact (Nat.find_spec (example_seq_set_infinite 0)).right
  · exact (Nat.find_spec (example_seq_set_infinite (exampleSeq n))).right

theorem example_seq_mono : ∀ (m n : Nat), m < n → exampleSeq m < exampleSeq n := by
  intros m n hmn
  induction n with
  | zero =>
    apply False.elim
    apply Nat.not_lt_zero m
    exact hmn
  | succ n' hsmn =>
    have hsn'n : exampleSeq n' < exampleSeq (n' + 1) := by
      exact (Nat.find_spec (example_seq_set_infinite (exampleSeq n'))).left
    refine lt_of_lt_of_le' hsn'n ?_
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_add_one hmn) with hmn' | hmn'
    · apply Nat.le_of_eq
      apply congrArg
      exact hmn'
    · apply Nat.le_of_lt
      apply hsmn
      exact hmn'

theorem example_seq_pos : ∀ n, 0 < exampleSeq n := by
  intro n
  have h : 0 < exampleSeq 0 := by
    unfold exampleSeq
    simp
  rcases n with _ | n'
  · exact h
  · trans exampleSeq 0
    · exact h
    · exact example_seq_mono 0 (n' + 1) (Nat.zero_lt_succ n')

theorem example_seq_inj : ∀ m n, m ≠ n → exampleSeq m ≠ exampleSeq n := by
  intros m n hmn
  rcases Nat.lt_or_gt_of_ne hmn with hmn' | hmn'
  · apply Nat.ne_of_lt
    exact example_seq_mono m n hmn'
  · apply Nat.ne_of_gt
    exact example_seq_mono n m hmn'

/-
theorem example_seq_add_ne_two_pow₁ :
  ∀ k m m' l, (2 ^ k) * (4 * m + 1) + (2 ^ k) * (4 * m' + 1) = 2 ^ l → m = m' := by
  intros k m m' l hm
  by_contra hsum
  rw [← Nat.left_distrib] at hsum
  have hkl : k < l := by
    apply (Nat.pow_lt_pow_iff_right (show 1 < 2 by simp)).mp
    rw [← hsum]
    conv =>
      lhs
      rw [← Nat.mul_one (2 ^ k)]
    apply Nat.mul_lt_mul_of_le_of_lt
    · simp
    · apply Nat.lt_of_add_one_le
      refine Nat.add_le_add ?_ ?_
      · simp
      · simp
    · simp
  obtain hsum := (Nat.div_eq_of_eq_mul_right (by simp) hsum.symm).symm
  conv at hsum =>
    rw [Nat.pow_div hkl.le (by simp)]
    rw [Nat.add_add_add_comm]
    rw [← Nat.left_distrib]
    simp
  by_cases hkl' : l ≤ k + 1
  · rw [← Nat.add_one_le_iff] at hkl
    obtain hkl' := Nat.eq_iff_le_and_ge.mpr ⟨hkl, hkl'⟩
    rw [← hkl'] at hsum
    simp at hsum
    rw [hsum.left, hsum.right] at hm
    simp at hm
  · simp at hkl'
    rw [Nat.add_comm, ← Nat.lt_sub_iff_add_lt] at hkl'
    have hd : 4 ∣ 2 ^ (l - k) := by
      rw [show 4 = 2 ^ 2 by simp]
      apply Nat.pow_dvd_pow
      exact hkl'.nat_succ_le
    rw [← hsum] at hd
    rw [← Nat.dvd_add_iff_right (show 4 ∣ 4 * (m + m') by simp)] at hd
    absurd hd
    simp
-/

theorem example_seq_add_ne_two_pow_of_exp_eq :
  ∀ k m m' l, m ≠ m' → 2 ^ k * (4 * m + 1) + 2 ^ k * (4 * m' + 1) ≠ 2 ^ l := by
  intros k m m' l hmm'
  by_contra h
  rw [← Distrib.left_distrib] at h
  have hkl : k < l := by
    rw [← pow_lt_pow_iff_right₀ (show 1 < 2 by simp), ← h]
    simp
    apply lt_add_of_le_of_pos <;> simp
  rw [← Nat.sub_add_cancel hkl.le, pow_add, mul_comm] at h
  rw [add_add_add_comm, ← Distrib.left_distrib] at h
  simp at h
  by_cases hkl' : l - k > 1
  · rw [← Nat.sub_add_cancel hkl', pow_add] at h
    absurd show 4 ∣ 2 ^ (l - k - 2) * 2 ^ 2 by simp
    rw [← h, ← Nat.dvd_add_iff_right (show 4 ∣ 4 * (m + m') by simp)]
    simp
  · rw [Nat.not_gt_eq] at hkl'
    rw [Nat.eq_iff_le_and_ge.mpr ⟨hkl', Nat.zero_lt_sub_of_lt hkl⟩] at h
    simp at h
    absurd hmm'
    rw [h.left, h.right]

/-
theorem example_seq_add_ne_two_pow₂ :
  ∀ k k' m m' l, (2 ^ k) * (4 * m + 1) + (2 ^ k') * (4 * m' + 1) = 2 ^ l → k ≤ k' := by
  intros k k' m m' l h
  have hkl : k < l := by
    rw [← pow_lt_pow_iff_right₀ (show 1 < 2 by simp), ← h]
    apply lt_of_le_of_lt (show 2 ^ k ≤ (2 ^ k) * (4 * m + 1) by simp)
    rw [Nat.lt_add_right_iff_pos]
    simp
  by_contra hkk'
  simp at hkk'
  rw [← Nat.add_one_le_iff] at hkl
  rw [← Nat.sub_add_cancel ] at h
  rw [← ]

  conv at h =>
    rw [← Nat.add_sub_of_le h.le, ← Nat.add_sub_of_le hkl.le]
    rw [Nat.pow_add, Nat.pow_add, Nat.mul_assoc, ← Nat.left_distrib]
    rw [Nat.mul_left_cancel_iff (by simp)]
  sorry
  intros k k' m m' l h
  by_contra hsum
  have hkl : k < l := by
    apply (Nat.pow_lt_pow_iff_right (show 1 < 2 by simp)).mp
    rw [← hsum]
    apply Nat.lt_of_le_of_lt (show 2 ^ k ≤ (2 ^ k) * (4 * m + 1) by simp)
    apply Nat.lt_add_right_iff_pos.mpr
    simp
  conv at hsum =>
    rw [← Nat.add_sub_of_le h.le, ← Nat.add_sub_of_le hkl.le]
    rw [Nat.pow_add, Nat.pow_add, Nat.mul_assoc, ← Nat.left_distrib]
    rw [Nat.mul_left_cancel_iff (by simp)]
  have hd : 2 ∣ 2 ^ (l - k) := by
    conv =>
      lhs
      rw [show 2 = 2 ^ 1 by simp]
    apply Nat.pow_dvd_pow
    exact Nat.le_sub_of_add_le' hkl
  rw [← hsum] at hd
  have hd' : 2 ∣ (2 ^ (k' - k)) * (4 * m' + 1) := by
    refine Dvd.dvd.mul_right ?_ (4 * m' + 1)
    conv =>
      lhs
      rw [show 2 = 2 ^ 1 by simp]
    apply Nat.pow_dvd_pow
    exact Nat.le_sub_of_add_le' h
  rw [← Nat.dvd_add_iff_left hd'] at hd
  have hd'' : 2 ∣ 4 * m := by
    refine Dvd.dvd.mul_right ?_ m
    simp
  rw [← Nat.dvd_add_iff_right hd''] at hd
  absurd hd
  simp
-/

theorem example_seq_add_ne_two_pow_of_exp_lt :
  ∀ k k' m m' l, k < k' → 2 ^ k * (4 * m + 1) + 2 ^ k' * (4 * m' + 1) ≠ 2 ^ l := by
  intros k k' m m' l hkk'
  by_contra h
  have hkl : k < l := by
    rw [← pow_lt_pow_iff_right₀ (show 1 < 2 by simp), ← h]
    apply lt_of_le_of_lt (show 2 ^ k ≤ (2 ^ k) * (4 * m + 1) by simp)
    rw [Nat.lt_add_right_iff_pos]
    simp
  rw [← Nat.sub_add_cancel hkk'.le, ← Nat.sub_add_cancel hkl.le] at h
  rw [pow_add, pow_add, mul_comm, mul_assoc] at h
  conv at h => lhs; right; right; rw [mul_comm]
  rw [← mul_assoc, ← Distrib.right_distrib, Nat.mul_left_inj (by simp)] at h
  rw [← Nat.sub_add_cancel (Nat.zero_lt_sub_of_lt hkk').nat_succ_le] at h
  rw [← Nat.sub_add_cancel (Nat.zero_lt_sub_of_lt hkl).nat_succ_le] at h
  simp at h
  rw [Nat.pow_add_one, Nat.pow_add_one] at h
  absurd show Even (2 ^ (l - k - 1) * 2) by simp
  rw [← h, Nat.even_add]
  rw [show 4 * m = 2 * (2 * m) by rw [← mul_assoc]; simp]
  simp

theorem example_seq_add_ne_two_pow : ¬ ∃ m n k, m ≠ n ∧ exampleSeq m + exampleSeq n = 2 ^ k := by
  by_contra h
  let ⟨n, n', l, ⟨hnn', h⟩⟩ := h
  let ⟨k, m, hn⟩ := example_seq_mem n
  let ⟨k', m', hn'⟩ := example_seq_mem n'
  rw [hn, hn'] at h
  absurd h
  by_cases hkk' : k = k'
  · rw [← hkk']
    apply example_seq_add_ne_two_pow_of_exp_eq
    by_contra hmm'
    absurd example_seq_inj n n' hnn'
    rw [hn, hn', hkk', hmm']
  · rcases lt_or_gt_of_ne hkk' with hkk' | hkk'
    · exact example_seq_add_ne_two_pow_of_exp_lt k k' m m' l hkk'
    · rw [add_comm]
      exact example_seq_add_ne_two_pow_of_exp_lt k' k m' m l hkk'

theorem example_seq_lt (r : Real) (hr : 2 ≤ r) : ∀ n, exampleSeq n < (n + 1 : Nat) * r := by
  intro n
  have h : exampleSeq n < (n + 1) * 2 := by
    by_contra ha
    simp at ha

    sorry
  sorry

/-
theorem noSeqForLtTwoMinMems (r : Real) (hr : r < 2) (m : Nat) (hm : 2 * (2 - r)⁻¹ - 1 < 2 ^ m)
  (seq : Nat → Nat) (ha : IsRSeq r seq) : ∀ n, n ≤ 2 ^ m → seq n < 2 ^ (m + 1) := by
  conv at hm =>
    rw [sub_lt_iff_lt_add]
    rw [← lt_mul_inv_iff₀ (show 0 < (2 - r)⁻¹ by apply inv_pos.mpr; apply sub_pos.mpr; exact hr)]
    rw [inv_inv]
    rw [sub_eq_add_neg, Distrib.left_distrib, mul_neg, ← sub_eq_add_neg, lt_sub_iff_add_lt']
    conv => rhs; rw [Distrib.right_distrib]
    simp
    rw [show (2 ^ m * 2 : Real) = (2 ^ m * 2 : Nat) by simp, ← Nat.pow_add_one]
  have hm : seq (2 ^ m) < 2 ^ (m + 1) := by
    rw [show seq (2 ^ m) < 2 ^ (m + 1) ↔ (seq (2 ^ m) : Real) < (2 ^ (m + 1) : Nat)
      from Nat.cast_lt.symm]
    trans (2 ^ m + 1) * r
    · have ha' := ha.lt (2 ^ m)
      simp at ha'
      exact ha'
    · exact hm
  intros n hn
  rcases hn.lt_or_eq with hn | hn
  · rw [show seq n < 2 ^ (m + 1) ↔ (seq n : Real) < (2 ^ (m + 1) : Nat) from Nat.cast_lt.symm]
    trans (n + 1) * r
    · exact ha.lt n
    · refine lt_of_le_of_lt' ?_ (show (n + 1) * r < (n + 1) * 2 from ?_)
      · rw [← Nat.cast_add_one, show (2 : Real) = (2 : Nat) from rfl, ← Nat.cast_mul]
        rw [Nat.cast_le, Nat.pow_add_one]
        simp
        exact hn.nat_succ_le
      · apply mul_lt_mul_of_pos_left hr
        rw [show (0 : Real) = (0 : Nat) by simp, ← Nat.cast_add_one, Nat.cast_lt]
        simp
  · rw [hn]
    exact hm

theorem noSeqForLtTwoMaxMems (r : Real) (m : Nat) (seq : Nat → Nat) (ha : IsRSeq r seq) :
  ¬ ∀ n, n ≤ 2 ^ m → seq n < 2 ^ (m + 1) := by
  by_contra ha'
  let seq' (n : Nat) : Nat := (if seq n ≤ 2 ^ m then seq n else 2 ^ (m + 1) - seq n) - 1
  let pigeons := Finset.range (2 ^ m + 1)
  let pigeonHoles := Finset.range (2 ^ m )
  have hp : ∃ n ∈ pigeons, ∃ n' ∈ pigeons, n ≠ n' ∧ seq' n = seq' n' := by
    refine Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (show pigeonHoles.card < pigeons.card from ?_) ?_
    · rw [Finset.card_range, Finset.card_range]
      simp
    · intros n hn
      rw [Finset.mem_range, ← Nat.le_iff_lt_add_one] at hn
      apply Finset.mem_range.mpr
      unfold seq'
      split_ifs with hn'
      · refine (Nat.sub_lt_iff_lt_add' ?_).mpr ?_
        · exact ha.pos n
        · apply Nat.le_iff_lt_add_one.mp
          exact hn'
      · simp at hn'
        refine (Nat.sub_lt_iff_lt_add' ?_).mpr ?_
        · apply Nat.one_le_iff_ne_zero.mpr
          apply Nat.ne_zero_iff_zero_lt.mpr
          apply Nat.zero_lt_sub_of_lt
          apply ha'
          exact hn
        · apply Nat.le_iff_lt_add_one.mp
          apply Nat.sub_le_iff_le_add.mpr
          rw [Nat.pow_add_one, Nat.mul_two]
          apply (add_le_add_iff_left (2 ^ m)).mpr
          exact hn'.le
  have hp' : ∀ n ∈ pigeons, seq' n + 1 = seq n ∨ (seq' n + 1) + seq n = 2 ^ (m + 1) := by
    intros n hn
    unfold pigeons at hn
    rw [Finset.mem_range] at hn
    rw [Nat.lt_add_one_iff] at hn
    unfold seq'
    split_ifs
    · apply Or.inl
      apply Nat.sub_add_cancel
      exact ha.pos n
    · apply Or.inr
      have hn' : 1 ≤ 2 ^ (m + 1) - seq n := by
        apply Nat.one_le_iff_ne_zero.mpr
        apply Nat.ne_zero_iff_zero_lt.mpr
        apply Nat.zero_lt_sub_of_lt
        exact ha' n hn
      rw [Nat.sub_add_cancel hn']
      rw [Nat.sub_add_cancel (ha' n hn).le]
  obtain ⟨n, ⟨hn, ⟨n', ⟨hn', ⟨hnn', hsnn'⟩⟩⟩⟩⟩ := hp
  rcases hp' n hn with hp'n | hp'n
  · rcases hp' n' hn' with hp'n' | hp'n'
    · rw [← hsnn', hp'n] at hp'n'
      absurd hnn'
      exact ha.inj n n' hp'n'
    · rw [← hsnn', hp'n] at hp'n'
      absurd ha.add_ne_pow_two
      refine ⟨n, n', m + 1, ?_⟩
      exact ⟨hnn', hp'n'⟩
  · rcases hp' n' hn' with hp'n' | hp'n'
    · rw [hsnn', hp'n'] at hp'n
      absurd ha.add_ne_pow_two
      refine ⟨n', n, m + 1, ?_⟩
      exact ⟨hnn'.symm, hp'n⟩
    · rw [← hsnn', ← hp'n] at hp'n'
      simp at hp'n'
      absurd hnn'.symm
      exact ha.inj n' n hp'n'
-/

theorem r_lt_two_bla {r : Real} (hr : r < 2) {seq : Nat → Nat} (h : IsRSeq r seq) {m : Nat}
  (hm : 2 * (2 - r)⁻¹ < 2 ^ m + 1) : ∀ n ≤ 2 ^ m, seq n < 2 ^ (m + 1) := by
  conv at hm =>
    rw [← lt_mul_inv_iff₀ (show 0 < (2 - r)⁻¹ by apply inv_pos.mpr; apply sub_pos.mpr; exact hr)]
    rw [inv_inv]
    rw [sub_eq_add_neg, Distrib.left_distrib, mul_neg, ← sub_eq_add_neg, lt_sub_iff_add_lt']
    conv => rhs; rw [Distrib.right_distrib]
    simp
    rw [show (2 ^ m * 2 : Real) = (2 ^ m * 2 : Nat) by simp, ← Nat.pow_add_one]
    rw [show (2 ^ m + 1 : Real) = (2 ^ m + 1 : Nat) by simp]
  have hm : seq (2 ^ m) < 2 ^ (m + 1) := by
    rw [show seq (2 ^ m) < 2 ^ (m + 1) ↔ (seq (2 ^ m) : Real) < (2 ^ (m + 1) : Nat)
      from Nat.cast_lt.symm]
    trans (2 ^ m + 1) * r
    · have ha' := h.lt (2 ^ m)
      simp at ha'
      exact ha'
    · exact hm
  intros n hn
  rcases hn.lt_or_eq with hn | hn
  · rw [show seq n < 2 ^ (m + 1) ↔ (seq n : Real) < (2 ^ (m + 1) : Nat) from Nat.cast_lt.symm]
    trans (n + 1) * r
    · exact h.lt n
    · refine lt_of_le_of_lt' ?_ (show (n + 1) * r < (n + 1) * 2 from ?_)
      · rw [← Nat.cast_add_one, show (2 : Real) = (2 : Nat) from rfl, ← Nat.cast_mul]
        rw [Nat.cast_le, Nat.pow_add_one]
        simp
        exact hn.nat_succ_le
      · apply mul_lt_mul_of_pos_left hr
        rw [show (0 : Real) = (0 : Nat) by simp, ← Nat.cast_add_one, Nat.cast_lt]
        simp
  · rw [hn]
    exact hm

end Proof

--#eval (List.range 25).map perfectSeq

-- ==============================

section Result

def solution : Set Real := {r | 2 ≤ r}

theorem proof : ∀ r : Real, r ∈ solution ↔ ∃ seq : Nat → Nat, IsRSeq r seq := by
  intro r
  constructor
  · intro hr
    use exampleSeq
    constructor
    · exact example_seq_pos
    · exact example_seq_inj
    · exact example_seq_add_ne_two_pow
    · exact example_seq_lt r hr
  · contrapose
    intro hr
    unfold solution at hr
    simp at hr
    by_contra ha
    obtain ⟨seq, ha⟩ := ha
    obtain ⟨m, hm⟩ := exists_nat_gt (2 * (2 - r)⁻¹ - 1)
    have hm : 2 * (2 - r)⁻¹ - 1 < 2 ^ m := by
      trans (m : Real)
      · exact hm
      · rw [show (2 : Real) = (2 : Nat) by rfl, ← Nat.cast_pow 2 m]
        apply Nat.cast_lt.mpr
        exact Nat.lt_two_pow_self
    --absurd noSeqForLtTwoMinMems r hr m hm seq ha
    --exact noSeqForLtTwoMaxMems r m seq ha
    sorry

end Result
