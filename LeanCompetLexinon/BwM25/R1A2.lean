import Mathlib.Data.Nat.Digits

section Problem

def lastNonZeroDigitAux (l : List Nat) : Nat := match l.find? (· ≠ 0) with
| some a => a
| none => 0

def lastNonZeroDigit (n : Nat) : Nat := lastNonZeroDigitAux (Nat.digits 10 n)

end Problem

-- =============================================

section Proof

end Proof

-- =============================================

section Result



end Result
