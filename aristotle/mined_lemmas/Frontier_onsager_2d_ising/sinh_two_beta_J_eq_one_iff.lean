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

lemma sinh_two_beta_J_eq_one_iff (J β : ℝ) (hJ : 0 < J) :
    Real.sinh (2 * β * J) = 1 ↔ β = Real.log (1 + Real.sqrt 2) / (2 * J) := by
  have harsinh : Real.arsinh 1 = Real.log (1 + Real.sqrt 2) := by rw [Real.arsinh]; norm_num
  have key : ∀ t : ℝ, Real.sinh t = 1 ↔ t = Real.log (1 + Real.sqrt 2) := by
    intro t
    constructor
    · intro h
      have h' := congrArg Real.arsinh h
      rwa [Real.arsinh_sinh, harsinh] at h'
    · intro h
      rw [h, ← harsinh, Real.sinh_arsinh]
  rw [key, eq_div_iff (by positivity : (2:ℝ) * J ≠ 0)]
  constructor <;> intro h <;> linarith

/-- **Onsager 2D Ising (formalized statement and Lean-checked reduction).**

The 2D square-lattice Ising model on the `m × n` torus is set up in `Frontier.Z`, its
free energy per site in `Frontier.freeEnergyDensity`, and Onsager's exact thermodynamic-limit
expression in `Frontier.onsagerFree`.  The theorem records:

* the partition function is strictly positive, so the free energy is well defined;
* the infinite-temperature base case: for every finite torus the free energy per site equals
  Onsager's expression evaluated at `β = 0` (both are `log 2`);
* the exact finite-size evaluation on the `2 × 2` torus;
* the Kramers–Wannier/Onsager critical point: `sinh (2βJ) = 1` exactly at
  `β = log (1 + √2) / (2J)`.
-/
