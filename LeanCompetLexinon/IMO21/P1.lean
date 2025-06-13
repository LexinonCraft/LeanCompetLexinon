import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Group.Nat.Even

section Problem

inductive Pile : Type where
| left
| right

structure Card (n : Nat) : Type where
  m : Nat
  hl : m ≥ n
  hu : m ≤ 2 * n

def Distribution (n : Nat) : Type := Card n → Pile

def IsPerfectSquare (m : Nat) : Prop := ∃ m' : Nat, m' ^ 2 = m

end Problem

-- ==============================

section Proof

theorem dings {n : Nat} (m : Nat) (he : Even m)
  (hl : m ^ 2 ≥ 2 * m + 4) (hu : (m + 4) ^ 2 ≤ 4 * m + 4) :
  ∀ d : Distribution n, ∃ (c1 c2 : Card n), c1 ≠ c2 ∧ d c1 = d c2 ∧ IsPerfectSquare (c1.m + c2.m) := by
  intro d
  let c1' : Card n := ⟨m + 1, sorry, sorry⟩
  let c2' : Card n := ⟨m + 2, sorry, sorry⟩
  let c3' : Card n := ⟨m + 3, sorry, sorry⟩
  cases d c1'
  · cases d c2'
    · use c1'
      use c2'

      sorry
    · sorry
  · cases d c2'
    · sorry
    · sorry

end Proof

-- ==============================

section Result

theorem proof : ∀ n : Nat, n ≥ 100 → ∀ d : Distribution n,
  ∃ (c1 c2 : Card n), c1 ≠ c2 ∧ d c1 = d c2 ∧ IsPerfectSquare (c1.m + c2.m) := by
  intros n hn d
  let k := Nat.findGreatest (fun k' => k' ^ 2 < 2 * n + 4) (2 * n + 3)
  sorry

end Result
