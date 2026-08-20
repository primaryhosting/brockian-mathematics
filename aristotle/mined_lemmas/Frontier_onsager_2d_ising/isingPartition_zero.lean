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

/-- The argument of the logarithm in Onsager's exact free energy formula for the
two-dimensional square-lattice Ising model with reduced coupling `K = βJ`. -/

lemma isingPartition_zero (m n : ℕ) [NeZero m] [NeZero n] :
    isingPartition m n 0 = 2 ^ (m * n) := by
  unfold isingPartition
  simp only [zero_mul, Real.exp_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.card_univ, Fintype.card_fun]
  simp [ZMod.card, pow_mul]

/-- Free-spin base case for the finite lattice: at zero coupling the exact finite-volume
free energy per site equals `log 2` for every lattice size. -/
