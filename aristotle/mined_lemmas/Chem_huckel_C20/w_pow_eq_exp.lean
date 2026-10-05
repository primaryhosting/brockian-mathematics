import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Finset Polynomial

set_option maxHeartbeats 1000000

/-! ## Generalities on eigenvalues of matrices -/

/-- A scalar `μ` is an eigenvalue of `M` iff `M - μ • 1` is singular. -/

lemma w_pow_eq_exp (k : ℕ) : w ^ k = Complex.exp ((2 * Real.pi * k / 20 : ℝ) * Complex.I) := by
  rw [w, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

