import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic

section Problem

abbrev Perm (n : Nat) : Type := Equiv.Perm (Fin n)

def nextSwap {n : Nat} [NeZero n] (perm : Perm n) (k : Nat) : (Fin n) × (Fin n) :=
  let i := perm.invFun (Fin.ofNat' n k)
  (i - 1, i + 1)

def simulate {n : Nat} [NeZero n] (init : Perm n) : Nat → Perm n
| 0 => init
| k + 1 =>
  let perm := simulate init k
  let (l, r) := nextSwap perm (k + 1)
  Equiv.trans perm (Equiv.swap l r)

end Problem

-- ==============================

section Proof

end Proof

-- ==============================

section Result

theorem proof : ∀ perm : Perm 2021, ∃ k < 2021,
  let (l, r) := nextSwap (simulate perm k) k; perm.toFun l < k ∧ k < perm.toFun r := by
  intro perm
  by_contra h

  sorry

end Result
