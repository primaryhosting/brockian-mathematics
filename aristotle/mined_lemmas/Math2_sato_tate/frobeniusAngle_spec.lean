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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open Filter Topology Set Polynomial

/-- The Sato–Tate density `(2/π) sin²θ` on the interval `[0, π]`. -/

lemma frobeniusAngle_spec (a : ℕ → ℤ)
    (hasse : ∀ p : ℕ, p.Prime → |(a p : ℝ)| ≤ 2 * Real.sqrt p) (p : ℕ) (hp : p.Prime) :
    (a p : ℝ) = 2 * Real.sqrt p * Real.cos (frobeniusAngle a p) := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hsqrt : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hden : (0:ℝ) < 2 * Real.sqrt p := by linarith
  have habs : |(a p : ℝ) / (2 * Real.sqrt p)| ≤ 1 := by
    rw [abs_div, abs_of_pos hden, div_le_one hden]
    exact hasse p hp
  rw [abs_le] at habs
  unfold frobeniusAngle
  rw [Real.cos_arccos habs.1 habs.2]
  field_simp

/-- **Sato–Tate.**  Let `a : ℕ → ℤ` be the trace-of-Frobenius function of a non-CM elliptic
curve over `ℚ` (so that `|a p| ≤ 2 √p` by the Hasse bound), and let
`θ_p = arccos (a_p / (2 √p))` be the associated Frobenius angles.  Then the Frobenius angles
are equidistributed with respect to the Sato–Tate measure `(2/π) sin²θ dθ` on `[0, π]`
if and only if, for every `m ≥ 1`, the `m`-th symmetric power Weyl sums
`(1/π(N)) ∑_{p ≤ N} U_m(cos θ_p)` tend to `0`; the latter is exactly the analytic input
(nonvanishing/analyticity of the symmetric power `L`-functions) supplied by the potential
automorphy theorems.

The first conjunct records, using the Hasse bound, that `θ_p` is indeed an angle in `[0, π]`
with `a_p = 2 √p cos θ_p`; the equivalence itself holds for any angles in `[0, π]`. -/
