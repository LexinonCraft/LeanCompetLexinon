import Mathlib.Logic.Function.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Nat.Dist

section Problem

--def distance (f : Fin 10 → Fin 10) : Nat := ∑ n : Fin 10, ((f n).toNat - (f n.succ).toNat)
def distance (f : Fin 10 → Fin 10) : Nat := sorry

def DistancePossible (d : Nat) : Prop := ∃ f : Fin 10 → Fin 10, Function.Injective f ∧
  distance f = d

structure Answer where
  dist20Possible : Bool
  dist25Possible : Bool

end Problem

-- =============================================

section Proof

end Proof

-- =============================================

section Result

def answer : Answer := {dist20Possible := true, dist25Possible := false}

theorem proof : (DistancePossible 20 ↔ answer.dist20Possible) ∧
  (DistancePossible 25 ↔ answer.dist25Possible) := by
  constructor
  · sorry
  · sorry

end Result
