import Mathlib

/-- `n` is a base-10 palindrome: its digit list equals its reverse. -/

def IsPalindrome10 (n : ℕ) : Prop :=
  Nat.digits 10 n = (Nat.digits 10 n).reverse

/-- The palindromic-primes conjecture (**OPEN**), recorded as an unproven
`def`: infinitely many primes are base-10 palindromes. -/
