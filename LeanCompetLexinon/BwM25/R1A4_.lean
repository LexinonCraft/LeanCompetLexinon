import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

section Problem

structure Cell where
  x : Nat
  y : Nat

instance Cell.instDecEq : DecidableEq Cell := by
  intro c₁ c₂
  rw [show c₁ = ⟨c₁.x, c₁.y⟩ by rfl, show c₂ = ⟨c₂.x, c₂.y⟩ by rfl]
  by_cases hx : c₁.x = c₂.x
  · by_cases hy : c₁.y = c₂.y
    · refine .isTrue ?_
      rw [hx, hy]
    · refine .isFalse ?_
      by_contra h
      absurd hy
      injection h
  · refine .isFalse ?_
    by_contra h
    absurd hx
    injection h

structure GameState where
  colorizedCells : Finset Cell

def GameState.init : GameState := ⟨∅⟩

structure Move where
  cellsToBeColorized : Finset Cell

def GameState.apply (state : GameState) (move : Move) : GameState :=
  ⟨state.colorizedCells ∪ move.cellsToBeColorized⟩

inductive StateWinnable : Nat → Nat → GameState → Prop where

end Problem

-- =============================================

section Proof

end Proof

-- =============================================

section Result

def answer : Set (Nat × Nat) := Set.univ

theorem proof : ∀ m ≥ 3, ∀ n ≥ 3, (m, n) ∈ answer ↔ StateWinnable m n .init := by
  sorry

end Result
