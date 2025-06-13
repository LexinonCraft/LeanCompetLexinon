import Mathlib.Data.Set.Basic

section Problem

structure RectDim : Type where
  m : Nat
  n : Nat
  hm : m ≥ 3
  hn : n ≥ 3
deriving Repr

variable (dim : RectDim)

structure Cell : Type where
  x : Nat
  y : Nat
deriving Repr

def IsRectCell (cell : Cell) : Prop := let m := dim.m; let n := dim.n;
  cell.x < dim.n ∧ cell.y < dim.m ∧ (cell.x = 0 ∨ cell.x = n - 1 ∨ cell.y = 0 ∨ cell.y = m - 1)

structure GameState : Type where
  isCellColorized : Cell → Prop

def GameState.init : GameState := ⟨fun _ => False⟩

def GameState.IsFinished (state : GameState) : Prop
  := ∀ cell : Cell, IsRectCell dim cell → state.isCellColorized cell

structure Move where
  isCellToBeColorized : Cell → Prop

def GameState.applyMove (state : GameState) (move : Move) : GameState
  := ⟨fun cell => state.isCellColorized cell ∨ move.isCellToBeColorized cell⟩

inductive Adjacent (cell1 cell2 : Cell) : Prop where
  | right (h : cell1.x + 1 = cell2.x ∧ cell1.y = cell2.y) : Adjacent cell1 cell2
  | left (h : cell1.x - 1 = cell2.x ∧ cell1.y = cell2.y) : Adjacent cell1 cell2
  | down (h : cell1.x = cell2.x ∧ cell1.y + 1 = cell2.y) : Adjacent cell1 cell2
  | up (h : cell1.x = cell2.x ∧ cell1.y - 1 = cell2.y) : Adjacent cell1 cell2

inductive Coherent : (Cell → Prop) → Prop where
  | empty : Coherent (fun _ => false)
  | single (cell : Cell) : Coherent (fun cell' => cell.x = cell'.x && cell.y = cell'.y)
  | add {filter : Cell → Bool} {cell1 : Cell} {cell2 : Cell}
    (h1 : filter cell1) (h2 : Adjacent cell1 cell2)
    : Coherent (fun cell => cell.x = cell2.x ∧ cell.y = cell2.y ∨ filter cell)

def Rectangular (filter : Cell → Prop) : Prop := ∃ (x1 y1 x2 y2 : Nat),
  ∀ cell : Cell, filter cell ↔ x1 ≤ cell.x ∧ cell.x ≤ x2 ∧ y1 ≤ cell.y ∧ cell.y ≤ y2

structure IsValidMove (move : Move) (state : GameState) : Prop where
  onlyRectFrameIsColorized : ∀ cell : Cell, move.isCellToBeColorized cell → IsRectCell dim cell
  noCellIsColorizedTwice : ∀ cell : Cell, ¬ (move.isCellToBeColorized cell ∧ state.isCellColorized cell)
  atLestOneCellIsColorized : ∃ cell : Cell, move.isCellToBeColorized cell
  colorizedAreaIsRectangular : Rectangular (fun cell => move.isCellToBeColorized cell)
  uncolorizedAreaIsCoherent : Coherent (fun cell => IsRectCell dim cell
    ∧ ¬ (state.isCellColorized cell) ∧ ¬ (move.isCellToBeColorized cell))

inductive StateWinnable : GameState → Prop where
  | lastMove (state : GameState) (move : Move) (hv : IsValidMove dim move state)
    (hf : (state.applyMove move).IsFinished dim) : StateWinnable state
  | intermediateMove (state : GameState) (ownMove : Move) (hv : IsValidMove dim ownMove state)
    (hn : ∀ oppMove : Move, IsValidMove dim oppMove state
    → StateWinnable ((state.applyMove ownMove).applyMove oppMove)) : StateWinnable state

def FirstPlayerHasStrategy : Prop := StateWinnable dim GameState.init

end Problem

-- =============================================

section Proof

variable {dim : RectDim}

/-
def squareCaseFirstMove : ValidMove dim .init := by sorry

def strategyForSquareCase {m : Nat} {hm : m ≥ 3} : Strategy ⟨m, m, hm, hm⟩ := by
  intros state hf
  cases state.isCellColorized ⟨0, 0⟩ with
  | true => sorry
  | false => exact ⟨⟨fun cell => cell.x = 0 && cell.y = 0⟩, by sorry⟩
-/

namespace SquareCase

def IsSymmetricState (dim : RectDim) (state : GameState) : Prop := ∀ cell : Cell, IsRectCell dim cell
  → (state.isCellColorized ⟨cell.x, cell.y⟩ ↔ state.isCellColorized ⟨cell.y, cell.x⟩)

def firstMove : Move := ⟨fun cell => cell.x = 0 ∧ cell.y = 0⟩

theorem firstMoveIsValid : IsValidMove dim firstMove GameState.init := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro cell
    intro h
    have hx : cell.x = 0 := h.left
    have hy : cell.y = 0 := h.right
    unfold IsRectCell
    rw [hx, hy]
    simp
    apply And.intro
    · exact Nat.lt_of_lt_of_le (by simp) dim.hn
    · exact Nat.lt_of_lt_of_le (by simp) dim.hm
  · unfold GameState.init
    simp
  · use ⟨0, 0⟩
    unfold firstMove
    simp
  · use 0
    use 0
    use 0
    use 0
    intro cell
    constructor
    · unfold firstMove
      simp
    · unfold firstMove
      simp
  · sorry

def reactToMove (oppMove : Move) : Move := ⟨fun ⟨x, y⟩ => oppMove.isCellToBeColorized ⟨y, x⟩⟩

theorem firstPlayerCanReact {oppMove : Move} {state : GameState} (hsy : IsSymmetricState dim state)
  (hsq : dim.m = dim.n) (hv : IsValidMove dim oppMove state)
  : IsValidMove dim (reactToMove oppMove) (state.applyMove oppMove) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro cell
    intro h
    unfold IsRectCell
    sorry
  · sorry
  · obtain ⟨⟨x, y⟩, h'⟩ := hv.atLestOneCellIsColorized
    use ⟨y, x⟩
    exact h'
  · sorry
  · sorry

theorem existsStrategy {dim : RectDim} (hsq : dim.m = dim.n) : FirstPlayerHasStrategy dim := by
  sorry

end SquareCase

end Proof

-- =============================================

section Result

def solution : Set RectDim := Set.univ

theorem proof : ∀ dim : RectDim, FirstPlayerHasStrategy dim := by
  intro ⟨m, n, hm, hn⟩
  cases Nat.decEq m n with
  | isTrue h => sorry
  | isFalse h => sorry

end Result
