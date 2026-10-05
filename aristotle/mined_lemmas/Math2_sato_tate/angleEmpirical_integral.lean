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
open scoped ENNReal NNReal BoundedContinuousFunction

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

open MeasureTheory Filter Topology Set

/-! ## The Sato–Tate measure -/

/-- The Sato–Tate measure on `ℝ`: the probability measure supported on `[0, π]` with
density `(2/π) · sin²θ` with respect to Lebesgue measure. -/

theorem angleEmpirical_integral (θ : ℕ → ℝ) (X : ℕ) (hX : (Nat.primesBelow X).card ≠ 0)
    (f : ℝ →ᵇ ℝ) :
    ∫ x, f x ∂(angleEmpirical θ X) =
      (∑ p ∈ Nat.primesBelow X, f (θ p)) / ((Nat.primesBelow X).card : ℝ) := by
  rw [angleEmpirical, if_neg hX, MeasureTheory.integral_smul_measure,
    MeasureTheory.integral_finset_sum_measure (fun i _ => (f.integrable _))]
  simp only [MeasureTheory.integral_dirac, smul_eq_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, div_eq_inv_mul]

/-! ## The Sato–Tate law -/

/-- The Sato–Tate law for a sequence of angles `θ : ℕ → ℝ`: the angles `θ p`, for `p` running
over the primes, are equidistributed with respect to the Sato–Tate measure `(2/π) sin²θ dθ`
on `[0, π]`, in the sense that averages of bounded continuous test functions over the primes
`p < X` converge, as `X → ∞`, to the integral against the Sato–Tate measure.

For a non-CM elliptic curve over `ℚ` (with `a p` its trace of Frobenius at `p`) this is the
Sato–Tate theorem of Clozel–Harris–Shepherd-Barron–Taylor. -/
