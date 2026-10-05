import Mathlib

/-- `n` is a base-10 palindrome: its digit list equals its reverse. -/

theorem eleven_dvd_of_palindrome_even_digits {n : ℕ}
    (h : IsPalindrome10 n) (he : Even (Nat.digits 10 n).length) :
    11 ∣ n :=
  Nat.eleven_dvd_of_palindrome (List.Palindrome.of_reverse_eq h.symm) he

