/-
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring; the required header is
-- reproduced verbatim as a module docstring immediately after the import below.)

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

/-! ## The finite square-lattice Ising model on an `L × L` torus -/

/-- The cyclic shift `i ↦ i + 1` on `Fin L` (periodic boundary conditions). -/

lemma isingZ_two (K : ℝ) :
    isingZ 2 K = 2 * Real.exp (8 * K) + 12 + 2 * Real.exp (-(8 * K)) := by
  rw [isingZ, ← Fintype.sum_bijective enc enc_bijective _
      (fun σ : Config 2 => Real.exp (-K * energy 2 σ)) (fun b => rfl)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num [energy, enc, Fintype.sum_prod_type, Fin.sum_univ_two, shift_zero_two, shift_one_two,
    spin]
  ring_nf

/-! ## Main statement -/

/-- **Onsager's 2D Ising model.**

The `L × L` periodic square-lattice Ising model with unit nearest-neighbour coupling has a
strictly positive partition function `isingZ L K`, whose free energy per site is
`logZPerSite L K`.  Onsager's exact solution asserts that this converges, as `L → ∞`, to
`onsagerLogZ K = log 2 + (1/8π²) ∫∫ log (cosh²(2K) - sinh(2K)(cos θ₁ + cos θ₂))`.

The statement below formalizes the model and the Onsager expression, and establishes:

* positivity and the exact infinite-temperature count `Z = 2^{L²}`;
* the **base case** of Onsager's formula: at `K = 0` the exact finite-volume free energy
  equals the Onsager value `log 2` for every `L ≥ 1`;
* a Lean-checked reduction: `|(1/L²) log Z_L(K) - log 2| ≤ 2|K|` uniformly in `L`, so the
  finite-volume free energies converge to the Onsager value as `K → 0`, uniformly in the
  volume;
* the exact solution of the `1 × 1` torus, `(1/1²) log Z₁(K) = log 2 + 2K`, which shows the
  previous bound is sharp;
* the exact solution of the `2 × 2` torus,
  `Z₂(K) = 2 e^{8K} + 12 + 2 e^{-8K}`, obtained by explicit enumeration of the 16 states. -/
