import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## The 2D Ising model on a periodic `m × n` lattice (a torus) -/

/-- Real value of an Ising spin: `true ↦ +1`, `false ↦ -1`. -/

theorem isingLogZDensity_zero (m n : ℕ) [NeZero m] [NeZero n] (J : ℝ) :
    isingLogZDensity m n J 0 = Real.log 2 := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [isingLogZDensity, isingZ_zero, Real.log_pow]
  push_cast
  field_simp

/-! ## The transfer-matrix reduction

The first (and decisive) step of Onsager's solution is the reduction of the two-dimensional
partition function on the `m × n` torus to the trace of the `m`-th power of a `2ⁿ × 2ⁿ`
transfer matrix.  This section proves that reduction. -/

/-- Sum over open paths: for any matrix `T` and any matrix `A`,
`∑_{paths} A(r_last, r_0) ∏ T(r_i, r_{i+1}) = tr (A Tʲ)`. -/
