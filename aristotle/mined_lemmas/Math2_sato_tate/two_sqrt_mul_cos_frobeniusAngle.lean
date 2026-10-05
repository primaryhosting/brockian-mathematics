/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open MeasureTheory Filter Topology Set

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma two_sqrt_mul_cos_frobeniusAngle {a : ℤ} {p : ℕ} (hp : 0 < p)
    (h : |(a : ℝ)| ≤ 2 * Real.sqrt p) :
    2 * Real.sqrt p * Real.cos (frobeniusAngle a p) = (a : ℝ) := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp)
  have h2 : 0 < 2 * Real.sqrt p := by linarith
  have habs : |(a : ℝ) / (2 * Real.sqrt p)| ≤ 1 := by
    rw [abs_div, abs_of_pos h2, div_le_one h2]
    exact h
  rw [frobeniusAngle, Real.cos_arccos (by cases abs_le.mp habs; linarith) (abs_le.mp habs).2]
  field_simp

/-- **Sato–Tate for a sequence of Frobenius traces.**  If `a p` is the trace of Frobenius at `p`
of a non-CM elliptic curve over `ℚ` (satisfying the Hasse bound `|a p| ≤ 2√p`), and if the
associated Frobenius angles `θ p = arccos (a p / (2√p))` obey the Sato–Tate law in its weak form,
then for `0 ≤ α ≤ β ≤ π` the proportion of primes `p < X` with `θ p ∈ [α, β]` converges to
`∫_α^β (2/π) sin²t dt`. -/
