import Mathlib.Order.Bounds.Defs
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Parity

section Problem

abbrev Country : ℕ → Type := Fin

structure FlightSchedule (k : ℕ) where
  connected : Country k → Country k → Prop
  irrefl : ∀ city, ¬connected city city
  symm : ∀ city1 city2, connected city1 city2 → connected city2 city1
  not_exists_global_hub : ¬∃ hub, ∀ city, hub = city ∨ connected hub city

def ExistHubs {k : ℕ} (n : ℕ) (fs : FlightSchedule k) : Prop :=
  ∀ cities : Finset (Country k), cities.card = n → ∃ hub, ∀ city ∈ cities,
  fs.connected hub city

end Problem

-- ==============================

section Proof

def IsConnectedInPairedFlightSchedule {k : ℕ} (a b : Country k) : Prop := a.val / 2 ≠ b.val / 2

lemma paired_flight_schedule_symm {k : ℕ} (city1 city2 : Country (2 * k))
  (h : IsConnectedInPairedFlightSchedule city1 city2) :
  IsConnectedInPairedFlightSchedule city2 city1 := by
  unfold IsConnectedInPairedFlightSchedule at h ⊢
  rw [ne_comm]
  exact h

lemma dings {k : ℕ} [NeZero k] {city : Country (2 * k)} (h : Even city.val) :
  (city + 1).val = city.val + 1 := by
  rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  have h' : city.val + 1 ≤ 2 * k := by
    rw [Nat.add_one_le_iff]
    exact Fin.isLt city
  cases h'.lt_or_eq with
    | inl h' =>
      rw [Nat.mod_eq_of_lt h']
    | inr h' =>
      absurd h
      rw [← Nat.even_add_one, h']
      simp

lemma not_connected_pairs {k : ℕ} [NeZero k] (city : Country (2 * k)) (h : Even city.val) :
  city ≠ city + 1 ∧ ¬ IsConnectedInPairedFlightSchedule city (city + 1) := by
  constructor
  · apply Fin.ne_of_val_ne
    rw [dings h]
    simp
  · unfold IsConnectedInPairedFlightSchedule
    simp
    rw [← Nat.mul_left_inj (show 2 ≠ 0 by simp), Nat.div_two_mul_two_of_even h, ← Nat.add_one_inj]
    symm
    rw [dings h]
    apply Nat.div_two_mul_two_add_one_of_odd
    apply Even.add_one
    exact h

def pairedFlightSchedule {k : ℕ} [NeZero k] : FlightSchedule (2 * k) := by
  refine ⟨IsConnectedInPairedFlightSchedule, ?_, ?_, ?_⟩
  · intro _
    unfold IsConnectedInPairedFlightSchedule
    simp
  · exact paired_flight_schedule_symm
  · by_contra ha
    obtain ⟨hub, ha⟩ := ha
    by_cases h : Even hub.val
    · absurd ha (hub + 1)
      simp
      apply not_connected_pairs
      exact h
    · absurd ha (hub - 1)
      simp
      --rw [Fin.sub_a]
      sorry

theorem generalizedProof {k : ℕ} [NeZero k] :
  IsGreatest {n | ∃ fs : FlightSchedule (2 * k), ExistHubs n fs} (k - 1) := by
  constructor
  · simp
    sorry
  · sorry

end Proof

-- ==============================

section Result

def solution : ℕ := 1011

theorem proof : IsGreatest {n | ∃ fs : FlightSchedule 2024, ExistHubs n fs} solution := by
  rw [show 2024 = 2 * 1012 by rfl]
  exact generalizedProof

end Result
