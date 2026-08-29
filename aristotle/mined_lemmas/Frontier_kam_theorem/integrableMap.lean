/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- The `n`-dimensional torus `𝕋ⁿ = (ℝ/ℤ)ⁿ`. -/
abbrev Torus (n : ℕ) : Type := Fin n → AddCircle (1 : ℝ)

/-- `W` parametrizes an invariant torus of the map `f` on which the dynamics is
conjugate to the rigid rotation by the frequency vector `ω`:
`f (W θ) = W (θ + ω)` for all angles `θ ∈ 𝕋ⁿ`. -/

noncomputable def integrableMap {n : ℕ} (freq : (Fin n → ℝ) → Torus n) :
    ((Fin n → ℝ) × Torus n) → ((Fin n → ℝ) × Torus n) :=
  fun p => (p.1, p.2 + freq p.1)

/-- **Base case of KAM.** For an integrable system, each action level set
`{I₀} × 𝕋ⁿ` is an invariant torus, on which the dynamics is the rotation by `freq I₀`. -/
