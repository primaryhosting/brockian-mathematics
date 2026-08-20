import Mathlib
namespace Brockian.StarOfDavid

/-- `(a+b).choose a * a! * b! = (a+b)!`. -/

private lemma choose_prod_identity (j r : ℕ) :
    (j + r + 1).choose j * (j + r + 2).choose (j + 2) * (j + r + 3).choose (j + 1)
      = (j + r + 1).choose (j + 1) * (j + r + 2).choose j * (j + r + 3).choose (j + 2) := by
  have h1 : (j + r + 1).choose j * j.factorial * (r + 1).factorial = (j + r + 1).factorial :=
    choose_mul_fact (by omega)
  have h2 : (j + r + 2).choose (j + 2) * (j + 2).factorial * r.factorial = (j + r + 2).factorial :=
    choose_mul_fact (by omega)
  have h3 : (j + r + 3).choose (j + 1) * (j + 1).factorial * (r + 2).factorial
      = (j + r + 3).factorial := choose_mul_fact (by omega)
  have h4 : (j + r + 1).choose (j + 1) * (j + 1).factorial * r.factorial = (j + r + 1).factorial :=
    choose_mul_fact (by omega)
  have h5 : (j + r + 2).choose j * j.factorial * (r + 2).factorial = (j + r + 2).factorial :=
    choose_mul_fact (by omega)
  have h6 : (j + r + 3).choose (j + 2) * (j + 2).factorial * (r + 1).factorial
      = (j + r + 3).factorial := choose_mul_fact (by omega)
  set K := j.factorial * (j + 1).factorial * (j + 2).factorial * r.factorial * (r + 1).factorial *
      (r + 2).factorial with hK
  have hKpos : 0 < K := by
    positivity
  refine Nat.eq_of_mul_eq_mul_right hKpos ?_
  have hL : ((j + r + 1).choose j * (j + r + 2).choose (j + 2) * (j + r + 3).choose (j + 1)) * K
      = (j + r + 1).factorial * (j + r + 2).factorial * (j + r + 3).factorial := by
    rw [← h1, ← h2, ← h3, hK]; ring
  have hR : ((j + r + 1).choose (j + 1) * (j + r + 2).choose j * (j + r + 3).choose (j + 2)) * K
      = (j + r + 1).factorial * (j + r + 2).factorial * (j + r + 3).factorial := by
    rw [← h4, ← h5, ← h6, hK]; ring
  rw [hL, hR]

/-- Abstract key step: divisibility of one triple gcd by the other. -/
