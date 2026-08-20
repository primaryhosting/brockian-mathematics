import Mathlib
namespace MS2.FibLucas

/-- Cassini's identity. The statement is cast to `ℤ`, since `(-1)^n` does not
make sense in `ℕ`. -/

theorem binet (n : ℕ) :
    (Nat.fib n : ℝ) = (((1+Real.sqrt 5)/2)^n - ((1-Real.sqrt 5)/2)^n) / Real.sqrt 5 :=
  Real.coe_fib_eq n

end MS2.FibLucas

