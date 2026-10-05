/-
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open Complex

/-- The standard symplectic vector space `ℝ^{2(n+1)}`, modelled as `ℂ^{n+1}` viewed as a
real vector space. -/
abbrev SympSpace (n : ℕ) : Type := EuclideanSpace ℂ (Fin (n + 1))

/-- The standard symplectic form on `ℂ^{n+1} ≅ ℝ^{2(n+1)}`:
`ω(z, w) = Im ⟪z, w⟫ = ∑ᵢ (xᵢ y'ᵢ - yᵢ x'ᵢ)`. -/

lemma re_coord_eq (v : SympSpace n) : ((Φ v) 0).re = (inner ℂ (pVec Φ) v : ℂ).re := by
  have hw : Φ (wVec Φ) = Complex.I • e₀ n := by simp [wVec]
  have h1 : (inner ℂ (wVec Φ) v : ℂ).im = -((Φ v) 0).re := by
    have h := hΦ (wVec Φ) v
    rw [hw] at h
    rw [omegaForm, omegaForm, inner_smul_left, inner_e₀_left] at h
    simp at h
    linarith [h]
  rw [pVec, inner_smul_left]
  simp [h1]

/-- The two representing vectors are large enough: `‖p‖ * ‖q‖ ≥ 1`.  This is where the
symplectic condition enters: `p` and `q` are (up to multiplication by `i`) a pair of vectors
with `ω = 1`, hence by Cauchy-Schwarz their norms multiply to at least `1`. -/
