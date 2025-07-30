/-
Copyright (c) Lexinon. All rights reserved.
Licensed under the MIT license. See LICENSE file in the project root for details.
-/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Fin.Basic

/-!
# BwM24 R2 A4

In the country of Sikinia there are `2024` cities. Some of these are connected via direct,
bidirectional flight connections. No city is connected to all other cities. However, there is a
positive integer `n` such that for any `n` cities, there is another city connected to all `n` cities.
The contestants are asked to determine the greatest value that `n` can have.

It will be shown that the greatest value of `n` is `1011`. In fact, in a country with `k` cities
(where `k` is an arbitrary `Nat`, but at least `2`) `n` matches the above condition if and only if
`n < k / 2` (where `/` is the division operator for natural numbers).

## TODO

* Add more information about the solution to the header
* Add computable functions
-/

namespace BwM24R2A4

section Problem

/-! ## Definitions for setting up the problem -/

/-- `City k` is the type of a city in a country with `k` cities. -/
abbrev City : ℕ → Type := Fin

/-- A flight schedule defining for each two cities whether they are connected (without any
restrictions yet). -/
structure FlightSchedule (k : ℕ) where
  /-- `True` if and only if `city₁` and `city₂` are connected in this flight schedule.  -/
  connected (city₁ city₂ : City k) : Prop

/-- A flight schedule is valid if no city is connected to itself, the connections are
symmetric and there is no global hub connected to all other cities. -/
structure IsValidFlightSchedule {k : ℕ} (fs : FlightSchedule k) : Prop where
  irrefl : ∀ city, ¬fs.connected city city
  symm : ∀ city1 city2, fs.connected city1 city2 → fs.connected city2 city1
  not_exists_global_hub : ¬∃ hub, ∀ city, hub = city ∨ fs.connected hub city

/-- For any `n` cities there is a hub connected to all selected cities in the given flight schedule. -/
def ExistHubs {k : ℕ} (n : ℕ) (fs : FlightSchedule k) : Prop :=
  ∀ cities : Finset (City k), cities.card = n → ∃ hub, ∀ city ∈ cities,
  fs.connected hub city

end Problem

-- ==============================

section Proof

/-! ## Lemmas and definitions for the proof -/

open Finset
open Fin.NatCast

/-- There exists a hub for `n ≤ k` selected cities out of `k` cities if and only if `n < nBound k`. -/
def nBound (k : ℕ) : ℕ := k / 2

instance instNeZeroNBound {k : ℕ} [Nat.AtLeastTwo k] : NeZero (nBound k) := by
  refine ⟨?_⟩
  unfold nBound
  rw [Nat.div_ne_zero_iff]
  simp
  exact Nat.AtLeastTwo.prop

lemma n_bound_sub_one_le_k {k : ℕ} : nBound k - 1 ≤ k := by
  unfold nBound
  calc
    _ ≤ k / 2 := by simp
    _ ≤ _ := by apply Nat.div_le_self

section ExistsFlightSchedule

/-! ### Proof that there exists a flight schedule for n < nBound k -/

variable {k : ℕ} [Nat.AtLeastTwo k] {selectedCities : Finset (City k)} {hub : City k}

/-- For each pair of (or group of three) cities, we choose a representative. -/
def pairRepr (city : City k) : City k :=
  if Odd city.val then city - 1
  else if city + 1 = k then 0
  else city

/-- An example of a flight schedule where for any `n < nBound k` selected cities, there is a hub. -/
def pairedFlightSchedule : FlightSchedule k :=
  ⟨fun city₁ city₂ ↦ pairRepr city₁ ≠ pairRepr city₂⟩

/-! The following three lemmas are used for proving that each city is not connected to at least
one other city in `pairedFlightSchedule`. -/

lemma not_hub_last_city (h_hub : ¬Odd hub.val ∧ hub + 1 = k) :
    hub ≠ 0 ∧ ¬pairedFlightSchedule.connected hub 0 := by
  constructor
  · rw [← Fin.cast_val_eq_self 0]
    rw [ne_eq, ← add_left_inj 1, h_hub.right]
    simp
    exact Nat.AtLeastTwo.ne_one
  · unfold pairedFlightSchedule pairRepr
    simp only [ne_eq, not_not]
    rw [ite_cond_eq_false _ _ (eq_false h_hub.left)]
    rw [ite_cond_eq_true _ _ (eq_true h_hub.right)]
    simp

lemma not_hub_odd_city (h_hub : Odd hub.val) :
    hub ≠ hub - 1 ∧ ¬pairedFlightSchedule.connected hub (hub - 1) := by
  constructor
  · rw [ne_eq, ← add_left_inj 1]
    simp
    exact Nat.AtLeastTwo.ne_one
  · unfold pairedFlightSchedule pairRepr
    simp only [ne_eq, not_not]
    rw [ite_cond_eq_true _ _ (eq_true h_hub)]
    have h : ¬Odd (hub - 1).val := by
      rw [Fin.val_sub_one_of_ne_zero (by apply Fin.ne_of_val_ne; exact Nat.ne_of_odd_add h_hub)]
      rw [← Nat.odd_add_one, Nat.sub_one_add_one (Nat.ne_of_odd_add h_hub)]
      exact h_hub
    have h' : ¬(hub - 1 + 1 = k) := by
      simp
      apply Fin.ne_of_val_ne
      exact Nat.ne_of_odd_add h_hub
    rw [ite_cond_eq_false _ _ (eq_false h)]
    rw [ite_cond_eq_false _ _ (eq_false h')]

lemma not_hub_even_city (h_hub : ¬Odd hub.val ∧ hub + 1 ≠ k) :
    hub ≠ hub + 1 ∧ ¬pairedFlightSchedule.connected hub (hub + 1) := by
  constructor
  · simp
    exact Nat.AtLeastTwo.ne_one
  · unfold pairedFlightSchedule pairRepr
    simp only [ne_eq, not_not]
    rw [ite_cond_eq_false _ _ (eq_false h_hub.left), ite_cond_eq_false _ _ (eq_false h_hub.right)]
    rw [eq_comm, add_sub_cancel_right]
    apply ite_cond_eq_true
    apply eq_true
    rw [Fin.ne_iff_vne, Fin.natCast_self, Fin.val_zero] at h_hub
    have h : hub.val + (1 : City k).val < k := by
      apply lt_of_le_of_ne
      · rw [show (1 : City k) = (1 : ℕ) by simp, Fin.val_natCast]
        rw [Nat.one_mod_eq_one.mpr Nat.AtLeastTwo.ne_one]
        rw [Nat.add_one_le_iff]
        simp
      · by_contra ha
        absurd h_hub.right
        rw [Fin.val_add, ← Nat.mod_self k]
        congr
    rw [Fin.val_add_eq_of_add_lt h, show (1 : City k) = (1 : ℕ) by simp, Fin.val_natCast]
    rw [Nat.one_mod_eq_one.mpr Nat.AtLeastTwo.ne_one, Nat.odd_add_one]
    exact h_hub.left

/-- `pairedFlightSchedule` is a valid flight schedule. -/
lemma paired_flight_schedule_is_valid : IsValidFlightSchedule (@pairedFlightSchedule k _) := by
  constructor
  · intro _
    unfold pairedFlightSchedule
    simp
  · unfold pairedFlightSchedule
    simp
    intros _ _ h
    rw [eq_comm]
    exact h
  · simp
    intro hub
    by_cases h : Odd hub.val
    · use hub - 1
      exact not_hub_odd_city h
    · by_cases h' : hub + 1 = k
      · use 0
        exact not_hub_last_city ⟨h, h'⟩
      · use hub + 1
        exact not_hub_even_city ⟨h, h'⟩

/-- The set of all pair/group representatives. -/
def allPairRepr : Finset (City k) := {city | Even city.val ∧ city.val + 1 ≠ k}

/-- The set of representatives of the pairs/groups with at least one selected city. -/
def selectedPairRepr (cities : Finset (City k)) : Finset (City k) :=
  cities.image pairRepr

/-- There are (at least) `nBound k` pairs/groups. -/
lemma card_all_pair_repr : nBound k ≤ #(@allPairRepr k) := by
  apply @Finset.le_card_of_inj_on_range _ allPairRepr _ (fun n ↦ (2 * n : ℕ))
  · intros i hi
    unfold allPairRepr
    simp
    unfold nBound at hi
    rw [← Nat.mul_div_cancel_left i (show 0 < 2 by simp)] at hi
    constructor
    · rw [Nat.mod_eq_of_lt (Nat.lt_of_div_lt_div hi)]
      simp
    · rw [Nat.mod_eq_of_lt (Nat.lt_of_div_lt_div hi)]
      by_contra ha
      rw [← ha, @Nat.div_eq_sub_mod_div (2 * i + 1) 2] at hi
      simp at hi
  · intros i hi j hj h
    unfold nBound at hi hj
    rw [← Nat.mul_div_cancel_left i (show 0 < 2 by simp)] at hi
    rw [← Nat.mul_div_cancel_left j (show 0 < 2 by simp)] at hj
    have hi := Nat.lt_of_div_lt_div hi
    have hj := Nat.lt_of_div_lt_div hj
    apply Nat.mul_left_cancel (show 0 < 2 by simp)
    rw [← Fin.val_cast_of_lt hi, ← Fin.val_cast_of_lt hj]
    congr

/-- There is a pair/group with no selected city. -/
lemma exists_city_mem_sdiff (h_cities : #selectedCities < nBound k) :
    ∃ city, city ∈ allPairRepr \ selectedPairRepr selectedCities := by
  conv => args; ext city; rw [Finset.mem_sdiff]
  apply Finset.exists_mem_notMem_of_card_lt_card
  calc
    _ ≤ #selectedCities := by unfold selectedPairRepr; apply Finset.card_image_le
    _ < nBound k := h_cities
    _ ≤ _ := card_all_pair_repr

/-- If `hub` is the representative of a pair/group with no selected cities, then every selected
city is connected to `hub`. -/
lemma paired_flight_schedule_connected {city : City k}
    (h_hub : hub ∈ allPairRepr \ selectedPairRepr selectedCities) (h_city : city ∈ selectedCities) :
    pairedFlightSchedule.connected hub city := by
  rw [Finset.mem_sdiff] at h_hub
  unfold allPairRepr at h_hub
  simp at h_hub
  rw [← Nat.not_odd_iff_even] at h_hub
  unfold pairedFlightSchedule
  by_contra ha
  absurd h_hub.right
  unfold selectedPairRepr
  rw [Finset.mem_image]
  use city
  refine ⟨h_city, ?_⟩
  conv at ha => lhs; unfold pairRepr
  rw [ite_cond_eq_false _ _ (eq_false h_hub.left.left)] at ha
  calc
    _ = _ := ha.symm
    _ = _ := ?_
  apply ite_cond_eq_false
  apply eq_false
  rw [← ne_eq, Fin.ne_iff_vne, Fin.natCast_self, Fin.val_zero]
  have h : hub.val + (1 : City k).val < k := by
    apply lt_of_le_of_ne
    · rw [show (1 : City k) = (1 : ℕ) by simp, Fin.val_natCast]
      rw [Nat.one_mod_eq_one.mpr Nat.AtLeastTwo.ne_one]
      rw [Nat.add_one_le_iff]
      simp
    · rw [show (1 : City k) = (1 : ℕ) by simp, Fin.val_natCast]
      rw [Nat.one_mod_eq_one.mpr Nat.AtLeastTwo.ne_one]
      exact h_hub.left.right
  rw [Fin.val_add_eq_of_add_lt h, show (1 : City k) = (1 : ℕ) by simp, Fin.val_natCast]
  rw [Nat.one_mod_eq_one.mpr Nat.AtLeastTwo.ne_one]
  simp

/-- For each `nBound k - 1` selected cities, there is a `hub` connected to all selected cities. -/
lemma existHubs_paired_flight_schedule : @ExistHubs k (nBound k - 1) pairedFlightSchedule := by
  intros selectedCities h_cities
  conv at h_cities =>
    rw [eq_comm]
    rw [Nat.sub_eq_iff_eq_add (show 1 ≤ nBound k by rw [Nat.one_le_iff_ne_zero]; apply NeZero.ne)]
    rw [eq_comm]
  have h_cities := le_of_eq h_cities
  rw [Nat.add_one_le_iff] at h_cities
  have ⟨hub, h_hub⟩ := exists_city_mem_sdiff h_cities
  use hub
  intros city h_city
  exact paired_flight_schedule_connected h_hub h_city

end ExistsFlightSchedule

section NotExistsFlightSchedule

/-! ### Proof that there is no flight schedule for n >= nBound k -/

variable {k : ℕ}

/-- One of the colors red, blue and gray (with latter being the initial color of the cities). -/
inductive Color where
| red : Color
| blue : Color
| gray : Color
deriving DecidableEq, Repr

/-- Inverts a color where red and blue are inverse colors and gray is its own inverse. -/
@[reducible]
def Color.invert : Color → Color
| red => blue
| blue => red
| gray => gray

@[simp]
lemma Color.invert_invert (color : Color) : color.invert.invert = color := by
  unfold Color.invert
  match color with
  | red => simp
  | blue => simp
  | gray => simp

@[simp]
lemma Color.invert_eq_gray {color : Color} : color.invert = .gray ↔ color = .gray := by
  constructor
  · intro h
    unfold Color.invert at h
    cases color
    · simp at h
    · simp at h
    · rfl
  · intro h
    rw [h]

/-- The type of a function assigning each city a color. -/
def ColorMap (k : ℕ) : Type := City k → Color

/-- Each non-gray city is diconnected from at least one inverse-colored city. -/
def NeighboursCondition (fs : FlightSchedule k) (colorMap : ColorMap k) : Prop :=
  ∀ city₁, colorMap city₁ ≠ .gray → ∃ city₂, ¬fs.connected city₁ city₂ ∧
  (colorMap city₁).invert = colorMap city₂

/-- In the given `colorMap` (assigning each city a color), at least `i` cities are non-gray and
the `NeighboursCondition` is fulfilled. -/
structure IsValidColorMap (fs : FlightSchedule k) (i : ℕ) (colorMap : ColorMap k) :
    Prop where
  card : i ≤ #{city | colorMap city ≠ .gray}
  neigh : NeighboursCondition fs colorMap

/-- All cities are colored (non-gray). -/
def IsCompleteColorMap (fs : FlightSchedule k) (colorMap : ColorMap k) : Prop :=
  IsValidColorMap fs k colorMap

variable {fs : FlightSchedule k} {colorMap : ColorMap k} {city₁ city₂ city : City k}

lemma card_filter_ne_gray (h : ¬∃ city, colorMap city = Color.gray) :
    k = #{city | colorMap city ≠ Color.gray} := by
  conv => lhs; rw [← Finset.card_fin k]
  rw [eq_comm, Finset.card_filter_eq_iff]
  intros city _
  by_contra
  absurd h
  use city

lemma all_cities_not_global_hub (h_fs : IsValidFlightSchedule fs) :
    ∀ hub, ∃ city, hub ≠ city ∧ ¬fs.connected hub city := by
  have h := h_fs.not_exists_global_hub
  simp at h
  exact h

/-- Turns an existing `colorMap` into a new one where all cities keep their color except for
`city₁`, which is assigned the inverse of the color of `city₂`. -/
def colorSingleCity (colorMap : ColorMap k) (city₁ city₂ : City k) : ColorMap k :=
  fun city' ↦ if city' = city₁ then (colorMap city₂).invert else colorMap city'

lemma color_single_city_card (h_city₁ : colorMap city₁ = .gray) (h_city₂ : colorMap city₂ ≠ .gray) :
    #{city' | colorMap city' ≠ .gray} + 1 ≤
    #{city' | (colorSingleCity colorMap city₁ city₂) city' ≠ .gray} := by
  rw [← @Finset.card_insert_of_notMem _ _ city₁ _ (by simp; exact h_city₁)]
  apply Finset.card_le_card
  intros city' h_city'
  simp at h_city'
  simp
  unfold colorSingleCity
  split_ifs with h_city'_city₁
  · simp
    exact h_city₂
  · rw [or_iff_not_imp_left] at h_city'
    exact h_city' h_city'_city₁

lemma color_single_city_neigh (h_color_map : NeighboursCondition fs colorMap)
    (h_city₁ : colorMap city₁ = .gray) (h_city₁_city₂ : ¬fs.connected city₁ city₂ ∧ city₁ ≠ city₂) :
    NeighboursCondition fs (colorSingleCity colorMap city₁ city₂) := by
  intros city'₁ h_city'₁
  unfold colorSingleCity at h_city'₁ ⊢
  split_ifs at h_city'₁ with h_city'₁_city₁
  · use city₂
    rw [h_city'₁_city₁]
    refine ⟨h_city₁_city₂.left, ?_⟩
    rw [ite_cond_eq_false _ _ (eq_false_intro h_city₁_city₂.right.symm)]
    simp
  · have ⟨city'₂, h_city'₂⟩ := h_color_map city'₁ h_city'₁
    use city'₂
    refine ⟨h_city'₂.left, ?_⟩
    have h_city'₂_city₁ : city'₂ ≠ city₁ := by
      by_contra ha
      absurd h_city'₂.right
      rw [ha, h_city₁]
      simp
      exact h_city'₁
    rw [ite_cond_eq_false _ _ (eq_false_intro h_city'₁_city₁)]
    rw [ite_cond_eq_false _ _ (eq_false_intro h_city'₂_city₁)]
    exact h_city'₂.right

/-- Turns an existing `colorMap` into a new one where all cities keep their color except for
`city₁` and `city₂`, which are assigned inverse colors. -/
def colorPairOfCities (colorMap : ColorMap k) (city₁ city₂ : City k) : ColorMap k :=
  fun city' ↦
  if city' = city₁ then .red
  else if city' = city₂ then .blue
  else colorMap city'

lemma color_pair_of_cities_card (h_city₁ : colorMap city₁ = .gray) :
    #{city' | colorMap city' ≠ .gray} + 1 ≤
    #{city' | (colorPairOfCities colorMap city₁ city₂) city' ≠ .gray} := by
  rw [← @Finset.card_insert_of_notMem _ _ city₁ _ (by simp; exact h_city₁)]
  apply Finset.card_le_card
  intros city' h_city'
  simp at h_city'
  simp
  unfold colorPairOfCities
  split_ifs with h
  · simp
  · simp
  · rw [or_iff_not_imp_left] at h_city'
    exact h_city' h

lemma color_pair_of_cities_neigh (h_fs : IsValidFlightSchedule fs)
    (h_color_map : NeighboursCondition fs colorMap)
    (h_city₁ : colorMap city₁ = .gray) (h_city₂ : colorMap city₂ = .gray)
    (h_city₁_city₂ : ¬fs.connected city₁ city₂ ∧ city₁ ≠ city₂) :
    NeighboursCondition fs (colorPairOfCities colorMap city₁ city₂) := by
  intros city'₁ h_city'₁
  unfold colorPairOfCities at h_city'₁ ⊢
  split_ifs at h_city'₁ with h_city'₁_city₁ h_city'₁_city₂
  · use city₂
    rw [h_city'₁_city₁]
    refine ⟨h_city₁_city₂.left, ?_⟩
    rw [ite_cond_eq_false _ _ (eq_false h_city₁_city₂.right)]
    rw [ite_cond_eq_false _ _ (eq_false h_city₁_city₂.right.symm)]
    simp
  · use city₁
    rw [h_city'₁_city₂]
    refine ⟨by by_contra; absurd h_city₁_city₂.left; apply h_fs.symm; assumption, ?_⟩
    rw [ite_cond_eq_false _ _ (eq_false h_city₁_city₂.right.symm)]
    rw [ite_cond_eq_false _ _ (eq_false h_city₁_city₂.right)]
    simp
  · have ⟨city'₂, h_city'₂⟩ := h_color_map city'₁ h_city'₁
    use city'₂
    refine ⟨h_city'₂.left, ?_⟩
    have h_city'₂_city₁ : city'₂ ≠ city₁ := by
      by_contra ha
      absurd h_city'₂.right
      rw [← ha] at h_city₁
      rw [h_city₁, Color.invert_eq_gray]
      exact h_city'₁
    have h_city'₂_city₂ : city'₂ ≠ city₂ := by
      by_contra ha
      absurd h_city'₂.right
      rw [← ha] at h_city₂
      rw [h_city₂, Color.invert_eq_gray]
      exact h_city'₁
    rw [ite_cond_eq_false _ _ (eq_false h_city'₁_city₁)]
    rw [ite_cond_eq_false _ _ (eq_false h_city'₁_city₂)]
    rw [ite_cond_eq_false _ _ (eq_false h_city'₂_city₁)]
    rw [ite_cond_eq_false _ _ (eq_false h_city'₂_city₂)]
    exact h_city'₂.right

/-- For each `FlightSchedule` there exists a complete color map. -/
lemma exists_color_map (h_fs : IsValidFlightSchedule fs) : ∃ colorMap,
    IsCompleteColorMap fs colorMap := by
  have h (i : ℕ) (hi : i ≤ k) : ∃ colorMap, IsValidColorMap fs i colorMap := by
    induction i with
    | zero =>
      refine ⟨fun _ ↦ .gray, by simp, ?_⟩
      unfold NeighboursCondition
      simp
    | succ i h_ind =>
      have ⟨colorMap, h_color_map⟩ := h_ind (Nat.le_of_add_right_le hi)
      by_cases h_exists_city : ∃ city, colorMap city = .gray
      · have ⟨city₁, h_city₁⟩ := h_exists_city
        have ⟨city₂, h_city₂⟩ := all_cities_not_global_hub h_fs city₁
        by_cases h_city₂_gray : colorMap city₂ = .gray
        · use colorPairOfCities colorMap city₁ city₂
          constructor
          · calc
              _ ≤ #{city | colorMap city ≠ Color.gray} + 1 := by simp; exact h_color_map.card
              _ ≤ _ := color_pair_of_cities_card h_city₁
          · exact color_pair_of_cities_neigh h_fs h_color_map.neigh h_city₁ h_city₂_gray h_city₂.symm
        · use colorSingleCity colorMap city₁ city₂
          constructor
          · calc
              _ ≤ #{city | colorMap city ≠ Color.gray} + 1 := by simp; exact h_color_map.card
              _ ≤ _ := color_single_city_card h_city₁ h_city₂_gray
          · exact color_single_city_neigh h_color_map.neigh h_city₁ h_city₂.symm
      · refine ⟨colorMap, ?_, h_color_map.neigh⟩
        apply le_trans hi
        apply le_of_eq
        exact card_filter_ne_gray h_exists_city
  apply h
  simp

lemma invert_red_iff_ne_red_of_complete_color_map
    (h_color_map : IsCompleteColorMap fs colorMap) :
    (colorMap city).invert = .red ↔ ¬(colorMap city = .red) := by
  unfold Color.invert
  split
  case h_1 h_city =>
    simp
    exact h_city
  case h_2 h_city =>
    simp
    rw [h_city]
    simp
  case h_3 h_city =>
    absurd h_city
    have h := h_color_map.card
    rw [← not_lt] at h
    conv at h => args; rhs; rw [← Fintype.card_fin k]
    rw [Finset.card_lt_iff_ne_univ, not_ne_iff, Finset.eq_univ_iff_forall] at h
    simp at h
    exact h city

/-- The set of red cities in `colorMap`. -/
def redCities (colorMap : ColorMap k) : Finset (City k) :=
  {city | colorMap city = .red}

/-- The set of blue cities in `colorMap`. -/
def blueCities (colorMap : ColorMap k) : Finset (City k) :=
  {city | colorMap city = .blue}

/-- WLOG, we can assume that in the `colorMap`, there are at most `nBound k` red cities. -/
lemma exists_color_map_with_card (h_fs : IsValidFlightSchedule fs) :
    ∃ colorMap, IsCompleteColorMap fs colorMap ∧ #(redCities colorMap) ≤ nBound k := by
  have ⟨colorMap, h_color_map⟩ := exists_color_map h_fs
  by_cases h : #(redCities colorMap) ≤ nBound k
  · use colorMap
  · use (fun city ↦ (colorMap city).invert)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · conv => rhs; args; fun; args; ext; rw [ne_eq, Color.invert_eq_gray, ← ne_eq]
      exact h_color_map.card
    · intros city₁ h_city₁
      simp at h_city₁
      have ⟨city₂, h_city₂⟩ := h_color_map.neigh city₁ h_city₁
      use city₂
      refine ⟨h_city₂.left, ?_⟩
      congr
      exact h_city₂.right
    · unfold redCities at h ⊢
      conv =>
        lhs; args; fun; args; ext city; simp;
        rw [invert_red_iff_ne_red_of_complete_color_map h_color_map]
      rw [Finset.filter_not, Finset.card_sdiff (by simp), Nat.sub_le_iff_le_add]
      simp
      unfold nBound at h ⊢
      by_cases h_k : Even k
      · conv => lhs; rw [← Nat.div_two_mul_two_of_even h_k, mul_two]
        simp
        apply le_of_not_ge
        exact h
      · rw [Nat.not_even_iff_odd] at h_k
        conv => lhs; rw [← Nat.div_two_mul_two_add_one_of_odd h_k, mul_two]
        rw [Nat.add_one_le_iff]
        simp
        simp at h
        exact h

/-- We can select all red cities and suffiently many additional blue cities. -/
lemma exist_selected_cities {n : ℕ} (hn : nBound k ≤ n ∧ n ≤ k)
    (h_red_cities : #(redCities colorMap) ≤ nBound k) : ∃ selectedCities,
    redCities colorMap ⊆ selectedCities ∧ #selectedCities = n := by
  apply Finset.exists_superset_card_eq
  · exact le_trans h_red_cities hn.left
  · simp
    exact hn.right

lemma mem_selected_cities_of_red {selectedCities : Finset (City k)}
    (h_selected_cities : redCities colorMap ⊆ selectedCities) {city : City k}
    (h_city : colorMap city = .red) : city ∈ selectedCities := by
  apply Finset.mem_of_subset h_selected_cities
  unfold redCities
  simp
  exact h_city

/-- No city is connected to all red cities and all blue selected cities. -/
lemma not_exists_hub_of_color_map (h_fs : IsValidFlightSchedule fs)
    (h_color_map : IsCompleteColorMap fs colorMap)
    {selectedCities : Finset (City k)}
    (h_selected_cities : redCities colorMap ⊆ selectedCities) :
    ¬∃ hub, ∀ city ∈ selectedCities, fs.connected hub city := by
  by_contra ha
  have ⟨hub, h_hub⟩ := ha
  cases h : colorMap hub with
  | red =>
    absurd h_fs.irrefl
    simp
    use hub
    apply h_hub hub
    exact mem_selected_cities_of_red h_selected_cities h
  | blue =>
    have ⟨city, h_city⟩ := h_color_map.neigh hub (by rw [h]; simp)
    rw [eq_comm, h] at h_city
    absurd h_city.left
    apply h_hub city
    exact mem_selected_cities_of_red h_selected_cities h_city.right
  | gray =>
    absurd h_color_map.card
    simp
    conv => rhs; rw [← Finset.card_fin k]
    apply lt_of_le_of_ne
    · apply Finset.card_filter_le
    · rw [ne_eq, Finset.card_filter_eq_iff]
      simp
      use hub

end NotExistsFlightSchedule

/-- The proof generalized for a country with `k` cities. -/
theorem generalizedProof {k : ℕ} [Nat.AtLeastTwo k] :
    IsGreatest {n | n ≤ k ∧ ∃ fs : FlightSchedule k,
    IsValidFlightSchedule fs ∧ ExistHubs n fs} (nBound k - 1) := by
  constructor
  · refine ⟨n_bound_sub_one_le_k, ?_⟩
    use pairedFlightSchedule
    refine ⟨paired_flight_schedule_is_valid, existHubs_paired_flight_schedule⟩
  · rw [mem_upperBounds]
    intros n hn
    simp at hn
    have ⟨fs, h_fs⟩ := hn.right
    by_contra ha
    rw [← lt_iff_not_ge, Nat.lt_iff_add_one_le, Nat.sub_one_add_one (NeZero.ne _)] at ha
    have ⟨colorMap, h_color_map⟩ := exists_color_map_with_card h_fs.left
    have ⟨selectedCities, h_selected_cities⟩ :=
      exist_selected_cities ⟨ha, hn.left⟩ h_color_map.right
    absurd h_fs.right selectedCities h_selected_cities.right
    exact not_exists_hub_of_color_map h_fs.left h_color_map.left h_selected_cities.left

end Proof

-- ==============================

section Result

/-! ## The solution and the proof of its correctness -/

/-- The greatest amount of cities in a country with `2024` countries such there is always a hub
connected to all of them. -/
def solution : ℕ := 1011

/-- Proof that the above `solution` is correct. -/
theorem proof : IsGreatest {n | n ≤ 2024 ∧ ∃ fs : FlightSchedule 2024,
    IsValidFlightSchedule fs ∧ ExistHubs n fs} solution := by
  rw [show 2024 = 2 * 1012 by rfl]
  exact generalizedProof

end Result

end BwM24R2A4
