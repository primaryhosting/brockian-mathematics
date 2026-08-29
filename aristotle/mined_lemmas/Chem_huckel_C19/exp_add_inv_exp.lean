import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to precede any module documentation, so the requested
header comment appears immediately after the single `import Mathlib` line.)
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₉`, i.e. the Hückel matrix of the
carbon skeleton of a 19-membered annulene (with `α = 0`, `β = 1`). -/

lemma exp_add_inv_exp (θ : ℝ) :
    Complex.exp (θ * Complex.I) + (Complex.exp (θ * Complex.I))⁻¹
      = ((2 * Real.cos θ : ℝ) : ℂ) := by
  rw [← Complex.exp_neg, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

/-- The `k`-th Hückel eigenvector of `C₁₉`. -/
