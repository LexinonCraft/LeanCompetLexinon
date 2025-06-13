import Mathlib.Order.Bounds.Defs
import Mathlib.Data.Rel
import Mathlib.Order.Defs.Unbundled
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Nat.Even

section Problem

abbrev Country : Type := Nat

abbrev City (country : Country) : Type := Fin country

structure FlightSchedule (country : Country) : Type where
  rel : Rel (City country) (City country)
  symm : IsSymm (City country) rel
  irrefl : IsIrrefl (City country) rel
  noGlobalHub : ¬ ∃ hub : City country, ∀ city : City country, hub ≠ city → rel hub city

def HubsExist {country : Country} (schedule : FlightSchedule country) (n : Nat) : Prop
  := ∀ nCities : Finset (City country), nCities.card = n
  → ∃ hub : City country, ∀ city : nCities, schedule.rel hub city

def sikinia : Country := 2024

end Problem

-- =====================================

section Proof

def scheduleOfAntiPairs {k : Nat} [NeZero k] : FlightSchedule (2 * k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intros city1 city2
    exact ¬ (Even city1.toNat ∧ city1.toNat + 1 = city2.toNat
      ∨ Even city2.toNat ∧ city2.toNat + 1 = city1.toNat
      ∨ city1 = city2)
  · constructor
    intros city1 city2 h
    by_contra h'
    cases h'
    · apply h
      apply Or.inr
      apply Or.inl
      assumption
    cases by assumption
    · apply h
      apply Or.inl
      assumption
    · apply h
      apply Or.inr
      apply Or.inr
      symm
      assumption
  · constructor
    intro city
    by_contra h'
    apply h'
    apply Or.inr
    apply Or.inr
    rfl
  · by_contra
    obtain ⟨hub, h⟩ := by assumption
    cases t : hub.toNat.instDecidablePredEven
    · let city : City (2 * k) := hub - 1
      have hn : hub ≠ city := by
        by_contra
        sorry
      apply h city hn
      apply Or.inr
      apply Or.inl
      sorry
    · sorry

theorem proofForScheduleOfAntiPairs {k : Nat} [NeZero k]
  : HubsExist (@scheduleOfAntiPairs k inferInstance) (k - 1) := by
  sorry

inductive Color : Type where
| red
| blue

def Coloring (country : Country) : Type := City country → Color

def PartColoring (country : Country) : Type := City country → Option Color

def colorizeCities {k : Nat} [NeZero k] (schedule : FlightSchedule (2 * k)) : Coloring (2 * k)
  := let rec helper : PartColoring (2 * k) → Nat → PartColoring (2 * k)
    | coloring, n + 1 => by sorry
    | coloring, 0 => by sorry
  sorry

def counterexample {k : Nat} [NeZero k] : FlightSchedule (2 * k) := by sorry

theorem generalizedProof (k : Nat) [NeZero k]
  : IsGreatest {n | ∃ f : FlightSchedule (2 * k), HubsExist f n} (k - 1) := by
  constructor
  · use scheduleOfAntiPairs
    exact proofForScheduleOfAntiPairs
  · intros n h
    cases h' : Classical.em (n ≤ k - 1)
    · assumption
    · sorry

end Proof

-- =====================================

section Result

def result : Nat := 1011

theorem proof : IsGreatest {n | ∃ f : FlightSchedule sikinia, HubsExist f n} result := by
  exact generalizedProof 1012

end Result
