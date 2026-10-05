import Mathlib

/-- `n` is a base-10 palindrome: its digit list equals its reverse. -/

def PalindromicPrimesInfinite : Prop :=
  {p : ℕ | p.Prime ∧ IsPalindrome10 p}.Infinite

/-- Every base-10 palindrome with an even number of digits is divisible by 11. -/
