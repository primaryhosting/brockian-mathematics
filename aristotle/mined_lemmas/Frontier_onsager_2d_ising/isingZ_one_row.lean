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

noncomputable section

/-! ## The model -/

/-- The real value `±1` of a spin encoded as a `Bool`. -/

theorem isingZ_one_row (n : ℕ) (K : ℝ) :
    isingZ 0 n K = Real.exp (K * (n + 1)) * ringZ n K := by
  rw [isingZ, ← Equiv.sum_comp (rowEquiv n), ringZ, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  have hb : isingBondSum 0 n (rowEquiv n τ)
      = (n + 1 : ℝ) + ∑ j : Fin (n + 1), spinVal (τ j) * spinVal (τ (j + 1)) := by
    simp only [isingBondSum, rowEquiv, Equiv.coe_fn_mk]
    rw [Finset.sum_add_distrib]
    simp [spinVal_mul_self]
  rw [hb, mul_add, Real.exp_add]

/-! ## Target -/

/-- **Onsager 2D Ising (formalization, base case and reduction).**

We set up the 2D square-lattice Ising model on the `(m+1) × (n+1)` torus and Onsager's
closed-form expression for the free energy per site, and we verify:

* the partition function is positive;
* at infinite temperature (`K = 0`) the finite-lattice partition function is `2^{sites}`,
  so the free energy per site is exactly `log 2`, and it agrees with the value
  `onsagerLogZ 0` produced by Onsager's formula (the infinite-temperature base case);
* the one-row torus (`m = 0`) reduces exactly to the periodic 1D Ising chain, whose
  partition function is `(2 cosh K)^N + (2 sinh K)^N` (exact transfer-matrix solution). -/
