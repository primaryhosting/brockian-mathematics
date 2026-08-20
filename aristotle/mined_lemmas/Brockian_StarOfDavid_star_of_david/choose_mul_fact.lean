import Mathlib
namespace Brockian.StarOfDavid

/-- `(a+b).choose a * a! * b! = (a+b)!`. -/

private lemma choose_mul_fact {a b n : ℕ} (h : n = a + b) :
    n.choose a * a.factorial * b.factorial = n.factorial := by
  subst h; exact choose_add_mul_factorial a b

/-- The product form of the Star of David theorem. -/
