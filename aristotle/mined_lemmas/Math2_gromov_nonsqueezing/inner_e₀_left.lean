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

lemma inner_e₀_left {n : ℕ} (z : SympSpace n) : (inner ℂ (e₀ n) z : ℂ) = z 0 := by
  simp [e₀, EuclideanSpace.inner_single_left]

