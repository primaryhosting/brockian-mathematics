/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a `/-! -/` module docstring,
-- because in Lean 4.28 a module docstring is a command and cannot precede `import`.
-- The same text is repeated below as the module docstring.)

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Hückel spectrum of the cyclic polyene C₁₉: the eigenvalues of the adjacency matrix of the
cycle graph `C₁₉` are exactly the numbers `2 cos (2πk/19)`, `k = 0, …, 18`.

The proof identifies the adjacency matrix with `S + S¹⁸`, where `S` is the cyclic shift matrix
(a circulant matrix), computes `spectrum ℂ S` (all 19-th roots of unity), and then applies the
spectral mapping theorem `spectrum.map_polynomial_aeval_of_degree_pos` for the polynomial
`X + X ^ 18`.
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Chem

open Matrix Complex Polynomial SimpleGraph

/-- A primitive 19-th root of unity. -/

lemma eval_eigenvalue (k : ℕ) :
    zeta19 ^ k + (zeta19 ^ k) ^ 18 = ((2 * Real.cos (2 * Real.pi * k / 19) : ℝ) : ℂ) := by
  set θ : ℝ := 2 * Real.pi * k / 19 with hθ
  have hz : zeta19 ^ k = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [zeta19, ← Complex.exp_nat_mul]
    congr 1
    rw [hθ]
    push_cast
    ring
  have h18 : (zeta19 ^ k) ^ 18 = Complex.exp (-(θ : ℂ) * Complex.I) := by
    rw [hz, ← Complex.exp_nat_mul]
    have key : ((18 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)
        = -(θ : ℂ) * Complex.I + ((k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [hθ]; push_cast; ring
    rw [key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h18, hz, ← Complex.two_cos, ← Complex.ofReal_cos]
  push_cast
  ring

/-- **Hückel theory for C₁₉.** The eigenvalues (spectrum) of the adjacency matrix of the cycle
graph `C₁₉` are exactly the numbers `2 cos (2πk/19)` for `k = 0, 1, …, 18`. -/
