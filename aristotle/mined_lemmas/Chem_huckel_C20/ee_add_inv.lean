import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Matrix Polynomial Finset

/-- A primitive 20-th root of unity. -/

lemma ee_add_inv (k : Fin 20) :
    ee k + (ee k)⁻¹ = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 20) : ℝ) : ℂ) := by
  have h := ee_eq_exp k
  set t : ℂ := ((2 * Real.pi * (k : ℕ) / 20 : ℝ) : ℂ) with ht
  rw [h, ← Complex.exp_neg, ← neg_mul]
  have : Complex.exp (t * Complex.I) + Complex.exp (-t * Complex.I) = 2 * Complex.cos t := by
    rw [Complex.cos]
    field_simp
  rw [this, ht, ← Complex.ofReal_cos]
  push_cast
  ring

/-- The characteristic polynomial of the adjacency matrix of the cycle graph `C₂₀`
(the Hückel matrix of the annulene C₂₀ with `α = 0`, `β = 1`) factors as
`∏_{k=0}^{19} (X - 2cos(2πk/20))`. -/
