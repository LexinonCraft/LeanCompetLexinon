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

def IsConnectedInPairedFlightSchedule {k : ℕ} (a b : Country k) : Prop := a.val / 2 ≠ b.val / 2

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

--#eval (@pairedFlightSchedule 5 _).connected 3 0

def allPairRepr : Finset (Country (2 * k)) :=
  (Finset.range k).image (fun n ↦ (2 * n : ℕ))

def selectedPairRepr : Finset (Country (2 * k)) :=
  cities.image (fun city ↦ (city.val / 2 * 2 : ℕ))

def findHub (cities : Finset (Country (2 * k))) : Country (2 * k) :=
  (allPairRepr \ selectedPairRepr cities).min.get!

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

lemma existHubs_paired_flight_schedule {k : ℕ} [NeZero k] :
    @ExistHubs (2 * k) (k - 1) pairedFlightSchedule := by
  intros cities h_cities
  have ⟨hub, h_hub⟩ := exists_city_mem_sdiff cities (le_of_eq h_cities)
  use hub
  intros city h_city
  exact paired_flight_schedule_connected h_hub h_city

/-
lemma existHubs_paired_flight_schedule {k : ℕ} [NeZero k] :
    @ExistHubs (2 * k) (k - 1) pairedFlightSchedule := by
  intros cities h_cities
  use findHub cities
  intros city h_city
  unfold pairedFlightSchedule IsConnectedInPairedFlightSchedule
  simp only
  apply find_hub_spec
  · exact le_of_eq h_cities
  · exact h_city
-/

inductive Color where
| red : Color
| blue : Color
| gray : Color
deriving DecidableEq, Repr

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
    unfold Color.invert
    simp

def NeighboursCondition (fs : FlightSchedule (2 * k)) (colorMap : Country (2 * k) → Color) : Prop :=
  ∀ city₁, colorMap city₁ ≠ .gray → ∃ city₂, ¬fs.connected city₁ city₂ ∧
  (colorMap city₁).invert = colorMap city₂

structure IsColoring (fs : FlightSchedule (2 * k)) (i : ℕ) (colorMap : Country (2 * k) → Color) :
    Prop where
  card : i ≤ #{city | colorMap city ≠ .gray}
  neigh : NeighboursCondition fs colorMap

omit [NeZero k] in
lemma dingsen {i : ℕ} (hi : i + 1 ≤ 2 * k) {colorMap : Country (2 * k) → Color}
    (h : ¬∃ city, colorMap city = Color.gray) : i + 1 ≤ #{city | colorMap city ≠ Color.gray} := by
  apply le_trans hi
  apply le_of_eq
  conv => lhs; rw [← Finset.card_fin (2 * k)]
  rw [eq_comm, Finset.card_filter_eq_iff]
  intros city _
  by_contra
  absurd h
  use city

omit [NeZero k] in
lemma blabli (fs : FlightSchedule (2 * k)) : ∀ hub, ∃ city, hub ≠ city ∧ ¬fs.connected hub city := by
  have h := fs.not_exists_global_hub
  simp at h
  exact h

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
  split_ifs with h
  · rw [Color.invert_eq_gray]
    exact h_city₂
  · rw [or_iff_not_imp_left] at h_city'
    exact h_city' h

omit [NeZero k] in
lemma color_single_city_neigh {fs : FlightSchedule (2 * k)} {colorMap : Country (2 * k) → Color}
    (h_color_map : NeighboursCondition fs colorMap) {city₁ city₂ : Country (2 * k)}
    (h_city₁ : colorMap city₁ = .gray) (h_city₁_city₂ : ¬fs.connected city₁ city₂ ∧ city₁ ≠ city₂) :
    NeighboursCondition fs (colorSingleCity colorMap city₁ city₂) := by
  intros city'₁ h_city'₁
  by_cases h : city'₁ = city₁
  · rw [h]
    use city₂
    refine ⟨h_city₁_city₂.left, ?_⟩
    unfold colorSingleCity
    conv => rhs; fun; fun; args; rw [eq_comm, eq_false h_city₁_city₂.right]
    simp
  · unfold colorSingleCity at h_city'₁
    conv at h_city'₁ => lhs; fun; fun; args; rw [eq_false h]
    simp [-ne_eq] at h_city'₁
    have ⟨city'₂, h_city'₂⟩ := h_color_map city'₁ h_city'₁
    use city'₂
    refine ⟨h_city'₂.left, ?_⟩
    have dings : city'₂ ≠ city₁ := by
      by_contra ha
      rw [← ha] at h_city₁
      rw [h_city₁, Color.invert_eq_gray] at h_city'₂
      absurd h_city'₁
      exact h_city'₂.right
    unfold colorSingleCity
    conv => lhs; args; fun; fun; args; rw [eq_false h]
    conv => rhs; fun; fun; args; rw [eq_false dings]
    exact h_city'₂.right

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
  unfold colorPairOfCities at h_city'₁
  split_ifs at h_city'₁ with h h'
  · use city₂
    rw [h]
    refine ⟨h_city₁_city₂.left, ?_⟩
    unfold colorPairOfCities Color.invert
    simp
    rw [eq_comm]
    apply ite_cond_eq_false
    simp
    rw [eq_comm]
    exact h_city₁_city₂.right
  · use city₁
    rw [h']
    refine ⟨by by_contra ha; absurd h_city₁_city₂.left; apply fs.symm; exact ha , ?_⟩
    unfold colorPairOfCities Color.invert
    simp
    conv => lhs; fun; fun; fun; right; fun; fun; args; rw [eq_comm, eq_false h_city₁_city₂.right]
    simp
  · have ⟨city'₂, h_city'₂⟩ := h_color_map city'₁ h_city'₁
    use city'₂
    refine ⟨h_city'₂.left, ?_⟩
    unfold colorPairOfCities
    conv => lhs; args; fun; fun; args; rw [eq_false h]
    conv => lhs; args; right; fun; fun; args; rw[eq_false h']
    have h_city'₂_city₁ : city'₂ ≠ city₁ := by
      by_contra ha
      absurd h_city'₂.right
      rw [← ha] at h_city₁
      rw [h_city₁, Color.invert_eq_gray]
      exact h_city'₁
    conv => rhs; fun; fun; args; rw [eq_false h_city'₂_city₁]
    have h_city'₂_city₂ : city'₂ ≠ city₂ := by
      by_contra ha
      absurd h_city'₂.right
      rw [← ha] at h_city₂
      rw [h_city₂, Color.invert_eq_gray]
      exact h_city'₁
    conv => rhs; right; fun; fun; args; rw [eq_false h_city'₂_city₂]
    exact h_city'₂.right

omit [NeZero k] in
lemma exists_coloring (fs : FlightSchedule (2 * k)) : ∃ colorMap,
    IsColoring fs (2 * k) colorMap := by
  have h (i : ℕ) (hi : i ≤ 2 * k) : ∃ colorMap, IsColoring fs i colorMap := by
    induction i with
    | zero =>
      refine ⟨fun _ ↦ .gray, by simp, ?_⟩
      unfold NeighboursCondition
      simp
    | succ i h_ind =>
      have ⟨colorMap, h_color_map⟩ := h_ind (Nat.le_of_add_right_le hi)
      by_cases h : ∃ city, colorMap city = .gray
      · have ⟨city₁, h_city₁⟩ := h
        have ⟨city₂, h_city₂⟩ := blabli fs city₁
        by_cases h' : colorMap city₂ = .gray
        · use colorPairOfCities colorMap city₁ city₂
          constructor
          · calc
              _ ≤ #{city | colorMap city ≠ Color.gray} + 1 := by simp; exact h_color_map.card
              _ ≤ _ := color_pair_of_cities_card h_city₁
          · exact color_pair_of_cities_neigh h_color_map.neigh h_city₁ h' h_city₂.symm
        · use colorSingleCity colorMap city₁ city₂
          constructor
          · calc
              _ ≤ #{city | colorMap city ≠ Color.gray} + 1 := by simp; exact h_color_map.card
              _ ≤ _ := color_single_city_card h_city₁ h'
          · exact color_single_city_neigh h_color_map.neigh h_city₁ h_city₂.symm
      · refine ⟨colorMap, ?_, h_color_map.neigh⟩
        exact dingsen hi h
  apply h
  simp

omit [NeZero k] in
lemma iuiuiui {fs : FlightSchedule (2 * k)} {colorMap : Country (2 * k) → Color}
    (h_color_map : IsColoring fs (2 * k) colorMap) {city : Country (2 * k)} :
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

omit [NeZero k] in
lemma iuiuiui' {fs : FlightSchedule (2 * k)} {colorMap : Country (2 * k) → Color}
    (h_color_map : IsColoring fs (2 * k) colorMap) {city : Country (2 * k)} :
    colorMap city = .blue ↔ ¬(colorMap city = .red) := by
  match h : colorMap city with
  | .red => simp
  | .blue => simp
  | .gray =>
    simp
    absurd h
    have h := h_color_map.card
    rw [← not_lt] at h
    conv at h => args; rhs; rw [← Fintype.card_fin (2 * k)]
    rw [Finset.card_lt_iff_ne_univ, not_ne_iff, Finset.eq_univ_iff_forall] at h
    simp at h
    exact h city

omit [NeZero k] in
lemma lilalu (fs : FlightSchedule (2 * k)) :
    ∃ colorMap, IsColoring fs (2 * k) colorMap ∧ #{city | colorMap city = .red} ≤ k := by
  have ⟨colorMap, h_color_map⟩ := exists_coloring fs
  by_cases h : #{city | colorMap city = .red} ≤ k
  · use colorMap
  · use (fun city ↦ (colorMap city).invert)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · conv => rhs; args; fun; args; ext; rw [ne_eq, Color.invert_eq_gray, ← ne_eq]
      exact h_color_map.card
    · intros city₁ h_city₁
      simp at h_city₁
      rw [Color.invert_eq_gray] at h_city₁
      have ⟨city₂, h_city₂⟩ := h_color_map.neigh city₁ h_city₁
      use city₂
      refine ⟨h_city₂.left, ?_⟩
      simp only
      congr
      exact h_city₂.right
    · conv =>
        lhs; args; fun; args; ext city; simp; rw [iuiuiui h_color_map]
      rw [Finset.filter_not, Finset.card_sdiff (by simp), Nat.sub_le_iff_le_add]
      conv => lhs; simp; rw [mul_comm, mul_two]
      simp
      simp at h
      exact h.le

def redCities (colorMap : Country (2 * k) → Color) : Finset (Country (2 * k)) :=
  {city | colorMap city = .red}

def blueCities (colorMap : Country (2 * k) → Color) : Finset (Country (2 * k)) :=
  {city | colorMap city = .blue}

omit [NeZero k] in
lemma elelele {fs : FlightSchedule (2 * k)} {colorMap : Country (2 * k) → Color}
    (h_color_map : IsColoring fs (2 * k) colorMap) :
    redCities colorMap ∪ blueCities colorMap = .univ := by
  conv => lhs; right; unfold blueCities; fun; args; ext city; rw [iuiuiui' h_color_map]
  unfold redCities
  apply Finset.filter_union_filter_neg_eq

omit [NeZero k] in
lemma lelelele {colorMap : Country (2 * k) → Color} :
    redCities colorMap ∩ blueCities colorMap = ∅ := by
  rw [← Finset.subset_empty]
  unfold redCities blueCities
  intro city h_city
  simp at h_city
  rw [h_city.left] at h_city
  simp at h_city

omit [NeZero k] in
lemma ashdj {fs : FlightSchedule (2 * k)} {colorMap : Country (2 * k) → Color}
    (h_color_map : IsColoring fs (2 * k) colorMap) {n : ℕ} (hn : n ≤ 2 * k) :
    ∃ cities ⊆ blueCities colorMap, #cities = n - #(redCities colorMap) := by
  apply Finset.exists_subset_card_eq
  rw [Nat.sub_le_iff_le_add, add_comm, ← Finset.card_union_add_card_inter]
  rw [elelele h_color_map, lelelele]
  simp
  exact hn

omit [NeZero k] in
lemma egge {n : ℕ} (hn : k ≤ n) {colorMap : Country (2 * k) → Color}
    (h_red_cities : #(redCities colorMap) ≤ k) {blueSelectedCities : Finset (Country (2 * k))}
    (h_blue_selected_cities : blueSelectedCities ⊆ blueCities colorMap ∧
    #blueSelectedCities = n - #(redCities colorMap)) :
    #(redCities colorMap ∪ blueSelectedCities) = n := by
  rw [Finset.card_union]
  have h : redCities colorMap ∩ blueSelectedCities = ∅ := by
    rw [← Finset.subset_empty]
    calc
      _ ⊆ redCities colorMap ∩ blueCities colorMap :=
        Finset.inter_subset_inter_left h_blue_selected_cities.left
      _ = _ := lelelele
  rw [h]
  simp
  rw [h_blue_selected_cities.right]
  apply Nat.add_sub_cancel'
  exact le_trans h_red_cities hn

omit [NeZero k] in
lemma supi {fs : FlightSchedule (2 * k)} {colorMap : Country (2 * k) → Color}
    (h_color_map : IsColoring fs (2 * k) colorMap)
    {blueSelectedCities : Finset (Country (2 * k))} :
    ¬∃ hub, ∀ city ∈ redCities colorMap ∪ blueSelectedCities, fs.connected hub city := by
  by_contra ha
  have ⟨hub, h_hub⟩ := ha
  have h : hub ∈ redCities colorMap ∪ blueCities colorMap := by
    rw [elelele h_color_map]
    simp
  simp at h
  cases h with
  | inl h =>
    absurd fs.irrefl
    simp
    use hub
    apply h_hub hub
    exact Finset.mem_union_left _ h
  | inr h =>
    unfold blueCities at h
    simp at h
    have ⟨city, h_city⟩ := h_color_map.neigh hub (by rw [h]; simp)
    absurd h_city.left
    apply h_hub
    apply Finset.mem_union_left
    unfold redCities
    simp
    rw [← h_city.right, h]
    unfold Color.invert
    simp

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
    simp at ha
    rw [Nat.lt_iff_add_one_le, Nat.sub_one_add_one (NeZero.ne k)] at ha
    have ⟨colorMap, h_color_map⟩ := lilalu fs
    have ⟨blueSelectedCities, h_blue_selected_cities⟩ := ashdj h_color_map.left hn.left
    absurd h_fs (redCities colorMap ∪ blueSelectedCities)
      (egge ha h_color_map.right h_blue_selected_cities)
    exact supi h_color_map.left

end Proof

-- ==============================

section Result

def solution : ℕ := 1011

theorem proof : IsGreatest {n | n ≤ 2024 ∧ ∃ fs : FlightSchedule 2024, ExistHubs n fs} solution := by
  rw [show 2024 = 2 * 1012 by rfl]
  exact generalizedProof

end Result
