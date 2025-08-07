/-
Copyright (c) Lexinon. All rights reserved.
Licensed under the MIT license. See LICENSE file in the project root for details.
-/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Finite.Defs
import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.Multiplicity

/-!
# Bwm25 R1 A2

For each integer $n\geq2$ consider the last non-zero digit of $n!$. The sequence of these digits starts
with $2,6,4,2,2,\dots$. The contestants are asked to determine the digits that appear in this sequence
and proof that each of them appears infinitely many times in the sequence.

It will be shown that the sequence only contains the digits $2,4,6,8$ (i. e. the non-zero even digits)
and each of them infinitely many times.
-/

namespace BwM25R1A2

section Problem

/-! ## Definitions for setting up the problem -/

def lastDigitFac (n : ℕ) : ℕ := ((Nat.digits 10 (Nat.factorial (n + 2))).find? (· ≠ 0)).get!

end Problem

-- ==============================

section Proof

/-! ## Lemmas and definitions for the proof -/

end Proof

-- ==============================

section Result

/-! ## The solution and the proof of its correctness -/

/-- The solution to the problem. -/
def solution : Set Nat := {2, 4, 6, 8}

/-- Proof that the above `solution` is correct. -/
theorem proof : solution = {d | ∃ n, lastDigitFac n = d} ∧
    ∀ d ∈ solution, Set.Infinite {n | lastDigitFac n = d} := by
  constructor
  · sorry
  · sorry

end Result

#eval (List.range 10).map lastDigitFac

end BwM25R1A2
