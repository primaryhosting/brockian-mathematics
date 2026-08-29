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

set_option grind.warning false

namespace Frontier

/-- The real value of an Ising spin: `true ↦ +1`, `false ↦ -1`. -/

lemma freeEnergyDensity_zero_beta (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (J : ℝ) :
    freeEnergyDensity m n 0 J = Real.log 2 := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [freeEnergyDensity, Z_zero_beta, Real.log_pow]
  push_cast
  field_simp

/-- The explicit enumeration of the sixteen spin configurations of the `2 × 2` torus. -/
