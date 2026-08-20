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

/-! ## The two-dimensional Ising model on a periodic square lattice -/

/-- The real spin value attached to a Boolean spin variable: `true ↦ +1`, `false ↦ -1`. -/

theorem isingPartition_eq_trace_transferMatrix (n : ℕ) (K : ℝ) :
    isingPartition n K = Matrix.trace (transferMatrix n K ^ (n + 1)) := by
  rw [trace_pow_eq_sum_cycles, isingPartition,
    ← Equiv.sum_comp (Equiv.curry (Fin (n + 1)) (Fin (n + 1)) Bool)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [transferMatrix, Matrix.of_apply, Equiv.curry_apply]
  rw [← Real.exp_sum]
  congr 1
  rw [bondSum_eq_rows, Finset.mul_sum]
  rfl

/-! ## Main statement -/

/-- **Onsager's solution of the two-dimensional Ising model** (formalised statement,
with the transfer-matrix reduction and the infinite-temperature case proved).

The conjuncts are:

0. positivity of the finite-volume partition function (so that the free energy
   density is well defined);
1. the exact transfer-matrix reduction of the finite-volume partition function,
   valid for every lattice size and every coupling;
2. the exact evaluation `Z_N(0) = 2^{N²}` of the partition function at infinite
   temperature, together with Onsager's formula giving the value `log 2` there;
3. the infinite-temperature case of Onsager's theorem: the finite-volume free
   energy densities converge, as the lattice size tends to infinity, to the value
   predicted by Onsager's exact expression. -/
