import Mathlib

/-!
# Det Eq Mertens 4
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Redheffer

/-- The `n × n` Redheffer matrix: entry `(i, j)` is `1` when `j = 0` (first column)
or when `i + 1` divides `j + 1` (using `1`-based indices), and `0` otherwise. -/

def redheffer (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if (j : ℕ) = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- The Mertens function `M n = ∑_{k=1}^{n} μ k`. -/
