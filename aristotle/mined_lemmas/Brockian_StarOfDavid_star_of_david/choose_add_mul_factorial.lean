import Mathlib
namespace Brockian.StarOfDavid

/-- `(a+b).choose a * a! * b! = (a+b)!`. -/

private lemma choose_add_mul_factorial (a b : ℕ) :
    (a + b).choose a * a.factorial * b.factorial = (a + b).factorial := by
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
  simpa using h

