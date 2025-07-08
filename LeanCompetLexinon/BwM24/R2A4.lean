import Mathlib.Order.Bounds.Defs
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Insert

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

open Finset

variable {k : ℕ} [NeZero k] (cities : Finset (Country (2 * k)))

lemma ne_zero_of_odd {n : ℕ} (h : Odd n) : n ≠ 0 := by
  by_contra ha; rw [Nat.odd_iff, ha] at h; simp at h

def IsConnectedInPairedFlightSchedule {k : ℕ} (a b : Country (2 * k)) : Prop := a.val / 2 ≠ b.val / 2

/-- If a global hub exists in the `pairedFlightSchedule`, it must be assigned an even number. -/
lemma even_global_hub {k : ℕ} [NeZero k] {hub : Country (2 * k)}
    (h : ∀ (city : Country (2 * k)), hub = city ∨ IsConnectedInPairedFlightSchedule hub city) :
    Even hub.val := by
  by_contra ha
  rw [Nat.not_even_iff_odd] at ha
  absurd h (hub - 1 : ℕ)
  have cast_val_eq : ((hub.val - 1 : ℕ) : Country (2 * k)).val = hub.val - 1 := by
    apply Fin.val_cast_of_lt
    calc
      _ ≤ hub.val := by simp
      _ < 2 * k := Fin.prop hub
  simp
  constructor
  · apply Fin.ne_of_val_ne
    rw [cast_val_eq, ne_comm]
    apply Nat.sub_one_ne_self
    exact ne_zero_of_odd ha
  · unfold IsConnectedInPairedFlightSchedule
    rw [ne_eq, not_not, ← Nat.mul_right_inj (show 2 ≠ 0 by simp), ← Nat.add_one_inj]
    rw [Nat.two_mul_div_two_add_one_of_odd ha, cast_val_eq, Nat.two_mul_div_two_of_even]
    · rw [eq_comm]; apply Nat.sub_one_add_one; exact ne_zero_of_odd ha
    · rw [← Nat.sub_one_add_one (ne_zero_of_odd ha), Nat.odd_add_one, Nat.not_odd_iff_even] at ha
      exact ha

/-- If a global hub exists in the `pairedFlightSchedule`, it must be assigned an odd number. -/
lemma not_even_global_hub {k : ℕ} [NeZero k] {hub : Country (2 * k)}
    (h : ∀ (city : Country (2 * k)), hub = city ∨ IsConnectedInPairedFlightSchedule hub city) :
    ¬Even hub.val := by
  by_contra ha
  absurd h (hub.val + 1 : ℕ)
  have cast_val_eq : ((hub.val + 1 : ℕ) : Country (2 * k)).val = hub.val + 1 := by
    apply Fin.val_cast_of_lt
    apply Nat.add_one_lt_of_even ha (by simp)
    exact Fin.prop hub
  simp
  constructor
  · apply Fin.ne_of_val_ne
    rw [cast_val_eq]
    simp
  · unfold IsConnectedInPairedFlightSchedule
    rw [ne_eq, not_not, ← Nat.mul_right_inj (show 2 ≠ 0 by simp), ← Nat.add_one_inj]
    rw [Nat.two_mul_div_two_of_even ha, cast_val_eq, Nat.two_mul_div_two_add_one_of_odd]
    rw [Nat.odd_add_one, Nat.not_odd_iff_even]
    exact ha

/-- A flight schedule where two different cities are not connected if and only if they are
assigned numbers where the greater number is odd and the successor of the other number. -/
def pairedFlightSchedule {k : ℕ} [NeZero k] : FlightSchedule (2 * k) := by
  refine ⟨IsConnectedInPairedFlightSchedule, ?_, ?_, ?_⟩
  · intro _
    unfold IsConnectedInPairedFlightSchedule
    simp
  · intros _ _
    unfold IsConnectedInPairedFlightSchedule
    rw [ne_comm]
    simp
  · by_contra ha
    let ⟨hub, ha⟩ := ha
    apply absurd (even_global_hub ha) (not_even_global_hub ha)

instance decidableConnectedInPairedFlightSchedule {k : ℕ} [NeZero k]
    (city1 city2 : Country (2 * k)) : Decidable (pairedFlightSchedule.connected city1 city2) := by
  unfold pairedFlightSchedule IsConnectedInPairedFlightSchedule; infer_instance

/-- All cities that are assigned an even number (each representing the pair consisting of the
city itself ans its successor). -/
def allPairRepr : Finset (Country (2 * k)) :=
  (Finset.range k).image (fun n ↦ (2 * n : ℕ))

/-- The representants of all selected cities. -/
def selectedPairRepr : Finset (Country (2 * k)) :=
  cities.image (fun city ↦ (city.val / 2 * 2 : ℕ))

/-
def findHub (cities : Finset (Country (2 * k))) : Country (2 * k) :=
  (allPairRepr \ selectedPairRepr cities).min.get!
-/

lemma card_all_pair_repr : #(@allPairRepr k _) = k := by
  unfold allPairRepr
  rw (config := { occs := .pos [8] }) [← Finset.card_range k]
  rw [Finset.card_image_iff]
  intros n₁ hn₁ n₂ hn₂ h
  rw [Finset.mem_coe, Finset.mem_range, ← Nat.mul_lt_mul_left (show 0 < 2 by simp)] at hn₁ hn₂
  simp at h
  rw [← Nat.mul_right_inj (show 2 ≠ 0 by simp), ← Fin.val_cast_of_lt hn₁, ← Fin.val_cast_of_lt hn₂]
  rw [Fin.val_eq_val]
  exact h

/-- There exists a pair of cities that are not selected ("unselected pair"). -/
lemma exists_city_mem_sdiff (h_cities : #cities ≤ k - 1) :
    ∃ city, city ∈ allPairRepr \ selectedPairRepr cities := by
  conv =>
    args; ext city; rw [Finset.mem_sdiff]
  apply Finset.exists_mem_not_mem_of_card_lt_card
  rw [card_all_pair_repr]
  rw (config := { occs := .pos [3] }) [← Nat.sub_one_add_one (NeZero.ne k)]
  rw [Nat.lt_add_one_iff]
  refine le_trans ?_ h_cities
  exact Finset.card_image_le

lemma even_hub (hub : Country (2 * k)) (h_hub : hub ∈ allPairRepr \ selectedPairRepr cities) :
    2 ∣ hub.val := by
  unfold allPairRepr at h_hub
  simp at h_hub
  have ⟨n, hn⟩ := h_hub.left
  rw [← Nat.mul_lt_mul_left (show 0 < 2 by simp)] at hn
  rw [← hn.right, Fin.val_cast_of_lt hn.left]
  simp

/-- A city of an unselected pair is connected to all selected cities. -/
lemma paired_flight_schedule_connected {cities : Finset (Country (2 * k))} {hub city : Country (2 * k)}
    (h_hub : hub ∈ allPairRepr \ selectedPairRepr cities) (h_city : city ∈ cities) :
    pairedFlightSchedule.connected hub city := by
  unfold pairedFlightSchedule FlightSchedule.connected IsConnectedInPairedFlightSchedule
  by_contra ha; absurd h_hub
  apply Finset.not_mem_sdiff_of_mem_right
  unfold selectedPairRepr
  rw [Finset.mem_image]
  use city
  refine ⟨h_city, ?_⟩
  rw [← ha, Nat.div_mul_cancel (even_hub cities hub h_hub), Fin.cast_val_eq_self]

/-
lemma find_hub_spec (h_cities : #cities ≤ k - 1) (city : Country (2 * k)) (h_city : city ∈ cities) :
    (findHub cities).val / 2 ≠ city.val / 2 := by
  unfold findHub
  have ⟨hub', h_hub'⟩ := exists_city_mem_sdiff cities h_cities
  have ⟨hub, h_hub⟩ := Finset.min_of_mem h_hub'
  rw [h_hub, ← WithTop.some_eq_coe, Option.get!_some]
  apply hub_div_two_ne_city_div_two cities hub city
  · exact Finset.mem_of_min h_hub
  · exact h_city
-/

--#eval @findHub 100 _ {0, 1, 2, 3, 4, 5, 6}

/-- For any `k - 1` selected cities there exists a hub connected to all of the selected cities. -/
lemma existHubs_paired_flight_schedule {k : ℕ} [NeZero k] :
    @ExistHubs (2 * k) (k - 1) pairedFlightSchedule := by
  intros cities h_cities
  have ⟨hub, h_hub⟩ := exists_city_mem_sdiff cities (le_of_eq h_cities)
  use hub
  intros city h_city
  exact paired_flight_schedule_connected h_hub h_city

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

/-- Each non-gray city is diconnected from at least one inverse-colored city. -/
def NeighboursCondition (fs : FlightSchedule (2 * k)) (colorMap : Country (2 * k) → Color) : Prop :=
  ∀ city₁, colorMap city₁ ≠ .gray → ∃ city₂, ¬fs.connected city₁ city₂ ∧
  (colorMap city₁).invert = colorMap city₂

/-- In the given `colorMap` (assigning each city a color), at least `i` cities are non-gray and
the `NeighboursCondition` is fulfilled. -/
structure IsIColorMap (fs : FlightSchedule (2 * k)) (i : ℕ) (colorMap : Country (2 * k) → Color) :
    Prop where
  card : i ≤ #{city | colorMap city ≠ .gray}
  neigh : NeighboursCondition fs colorMap

omit [NeZero k] in
lemma card_filter_ne_gray {colorMap : Country (2 * k) → Color}
    (h : ¬∃ city, colorMap city = Color.gray) : 2 * k = #{city | colorMap city ≠ Color.gray} := by
  conv => lhs; rw [← Finset.card_fin (2 * k)]
  rw [eq_comm, Finset.card_filter_eq_iff]
  intros city _
  by_contra
  absurd h
  use city

omit [NeZero k] in
lemma all_cities_not_global_hub (fs : FlightSchedule (2 * k)) :
    ∀ hub, ∃ city, hub ≠ city ∧ ¬fs.connected hub city := by
  have h := fs.not_exists_global_hub
  simp at h
  exact h

/-- Turns an existing `colorMap` into a new one where all cities keep their color except for
`city₁`, which is assigned the inverse of the color of `city₂`. -/
def colorSingleCity (colorMap : Country (2 * k) → Color) (city₁ city₂ : Country (2 * k))
    (city' : Country (2 * k)) : Color :=
  if city' = city₁ then (colorMap city₂).invert else colorMap city'

omit [NeZero k] in
lemma color_single_city_card {colorMap : Country (2 * k) → Color} {city₁ city₂ : Country (2 * k)}
    (h_city₁ : colorMap city₁ = .gray) (h_city₂ : colorMap city₂ ≠ .gray) :
    #{city' | colorMap city' ≠ .gray} + 1 ≤
    #{city' | (colorSingleCity colorMap city₁ city₂) city' ≠ .gray} := by
  rw [← @Finset.card_insert_of_not_mem _ _ city₁ _ (by simp; exact h_city₁)]
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

omit [NeZero k] in
lemma color_single_city_neigh {fs : FlightSchedule (2 * k)} {colorMap : Country (2 * k) → Color}
    (h_color_map : NeighboursCondition fs colorMap) {city₁ city₂ : Country (2 * k)}
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
def colorPairOfCities (colorMap : Country (2 * k) → Color) (city₁ city₂ : Country (2 * k))
    (city' : Country (2 * k)) : Color :=
  if city' = city₁ then .red
  else if city' = city₂ then .blue
  else colorMap city'

omit [NeZero k] in
lemma color_pair_of_cities_card {colorMap : Country (2 * k) → Color} {city₁ city₂ : Country (2 * k)}
    (h_city₁ : colorMap city₁ = .gray) : #{city' | colorMap city' ≠ .gray} + 1 ≤
    #{city' | (colorPairOfCities colorMap city₁ city₂) city' ≠ .gray} := by
  rw [← @Finset.card_insert_of_not_mem _ _ city₁ _ (by simp; exact h_city₁)]
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

omit [NeZero k] in
lemma color_pair_of_cities_neigh {fs : FlightSchedule (2 * k)} {colorMap : Country (2 * k) → Color}
    (h_color_map : NeighboursCondition fs colorMap) {city₁ city₂ : Country (2 * k)}
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
    refine ⟨by by_contra; absurd h_city₁_city₂.left; apply fs.symm; assumption, ?_⟩
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

omit [NeZero k] in
/-- For each `FlightSchedule` there exists a "complete" color map. -/
lemma exists_color_map (fs : FlightSchedule (2 * k)) : ∃ colorMap,
    IsIColorMap fs (2 * k) colorMap := by
  have h (i : ℕ) (hi : i ≤ 2 * k) : ∃ colorMap, IsIColorMap fs i colorMap := by
    induction i with
    | zero =>
      refine ⟨fun _ ↦ .gray, by simp, ?_⟩
      unfold NeighboursCondition
      simp
    | succ i h_ind =>
      have ⟨colorMap, h_color_map⟩ := h_ind (Nat.le_of_add_right_le hi)
      by_cases h_exists_city : ∃ city, colorMap city = .gray
      · have ⟨city₁, h_city₁⟩ := h_exists_city
        have ⟨city₂, h_city₂⟩ := all_cities_not_global_hub fs city₁
        by_cases h_city₂_gray : colorMap city₂ = .gray
        · use colorPairOfCities colorMap city₁ city₂
          constructor
          · calc
              _ ≤ #{city | colorMap city ≠ Color.gray} + 1 := by simp; exact h_color_map.card
              _ ≤ _ := color_pair_of_cities_card h_city₁
          · exact color_pair_of_cities_neigh h_color_map.neigh h_city₁ h_city₂_gray h_city₂.symm
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

omit [NeZero k] in
lemma invert_red_iff_ne_red_of_complete_color_map {fs : FlightSchedule (2 * k)}
    {colorMap : Country (2 * k) → Color}
    (h_color_map : IsIColorMap fs (2 * k) colorMap) {city : Country (2 * k)} :
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
    conv at h => args; rhs; rw [← Fintype.card_fin (2 * k)]
    rw [Finset.card_lt_iff_ne_univ, not_ne_iff, Finset.eq_univ_iff_forall] at h
    simp at h
    exact h city

/-- The set of red cities in `colorMap`. -/
def redCities (colorMap : Country (2 * k) → Color) : Finset (Country (2 * k)) :=
  {city | colorMap city = .red}

/-- The set of blue cities in `colorMap`. -/
def blueCities (colorMap : Country (2 * k) → Color) : Finset (Country (2 * k)) :=
  {city | colorMap city = .blue}

omit [NeZero k] in
/-- WLOG, we can assume that in the `colorMap`, there are at most `k` red cities. -/
lemma exists_color_map_with_card (fs : FlightSchedule (2 * k)) :
    ∃ colorMap, IsIColorMap fs (2 * k) colorMap ∧ #(redCities colorMap) ≤ k := by
  have ⟨colorMap, h_color_map⟩ := exists_color_map fs
  by_cases h : #(redCities colorMap) ≤ k
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
    · unfold redCities
      conv =>
        lhs; args; fun; args; ext city; simp;
        rw [invert_red_iff_ne_red_of_complete_color_map h_color_map]
      rw [Finset.filter_not, Finset.card_sdiff (by simp), Nat.sub_le_iff_le_add]
      conv => lhs; simp; rw [mul_comm, mul_two]
      simp
      simp at h
      exact h.le

omit [NeZero k] in
/-- We can select all red cities and suffiently many additional blue cities. -/
lemma exist_selected_cities {n : ℕ} (hn : k ≤ n ∧ n ≤ 2 * k) {colorMap : Country (2 * k) → Color}
    (h_red_cities : #(redCities colorMap) ≤ k) : ∃ selectedCities,
    redCities colorMap ⊆ selectedCities ∧ #selectedCities = n := by
  apply Finset.exists_superset_card_eq
  · exact le_trans h_red_cities hn.left
  · simp
    exact hn.right

omit [NeZero k] in
lemma mem_selected_cities_of_red {colorMap : Country (2 * k) → Color}
    {selectedCities : Finset (Country (2 * k))}
    (h_selected_cities : redCities colorMap ⊆ selectedCities) {city : Country (2 * k)}
    (h_city : colorMap city = .red) : city ∈ selectedCities := by
  apply Finset.mem_of_subset h_selected_cities
  unfold redCities
  simp
  exact h_city

omit [NeZero k] in
/-- No city is connected to all red cities and all blue selected cities. -/
lemma not_exists_hub_of_color_map {fs : FlightSchedule (2 * k)} {colorMap : Country (2 * k) → Color}
    (h_color_map : IsIColorMap fs (2 * k) colorMap) {selectedCities : Finset (Country (2 * k))}
    (h_selected_cities : redCities colorMap ⊆ selectedCities) :
    ¬∃ hub, ∀ city ∈ selectedCities, fs.connected hub city := by
  by_contra ha
  have ⟨hub, h_hub⟩ := ha
  cases h : colorMap hub with
  | red =>
    absurd fs.irrefl
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
    conv => rhs; rw [← Finset.card_fin (2 * k)]
    apply lt_of_le_of_ne
    · apply Finset.card_filter_le
    · rw [ne_eq, Finset.card_filter_eq_iff]
      simp
      use hub

/-- The proof generalized for a country with `2 * k` cities. -/
theorem generalizedProof {k : ℕ} [NeZero k] :
  IsGreatest {n | n ≤ 2 * k ∧ ∃ fs : FlightSchedule (2 * k), ExistHubs n fs} (k - 1) := by
  constructor
  · refine ⟨by trans k; simp; apply Nat.le_mul_of_pos_left k (show 0 < 2 by simp), ?_⟩
    use pairedFlightSchedule
    intros cities h_cities
    have ⟨hub, h_hub⟩ := exists_city_mem_sdiff cities (le_of_eq h_cities)
    use hub
    intros city h_city
    exact paired_flight_schedule_connected h_hub h_city
  · rw [mem_upperBounds]
    intros n hn
    simp at hn
    have ⟨fs, h_fs⟩ := hn.right
    by_contra ha
    rw [← lt_iff_not_ge, Nat.lt_iff_add_one_le, Nat.sub_one_add_one (NeZero.ne k)] at ha
    have ⟨colorMap, h_color_map⟩ := exists_color_map_with_card fs
    have ⟨selectedCities, h_selected_cities⟩ :=
      exist_selected_cities ⟨ha, hn.left⟩ h_color_map.right
    absurd h_fs selectedCities h_selected_cities.right
    exact not_exists_hub_of_color_map h_color_map.left h_selected_cities.left

end Proof

-- ==============================

section Result

def solution : ℕ := 1011

theorem proof : IsGreatest {n | n ≤ 2024 ∧ ∃ fs : FlightSchedule 2024, ExistHubs n fs} solution := by
  rw [show 2024 = 2 * 1012 by rfl]
  exact generalizedProof

end Result

/-
# TODO
* Rename lemmas to more meaningful names (check)
* Generalize to arbitrary amount of cities
* Add comments (kinda)
* Simplify proof for neighbourhood condition in colorSingleCity (check)
* Use more section variables
* Add computable functions
* Use redCities / blueCities definition where appropriate (check)
* Squish tactic proofs
* `IsIColorMap` should include color map
-/
