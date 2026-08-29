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

theorem isingZ_eq_trace_transferMatrix (m n : ℕ) [NeZero m] [NeZero n] (J β : ℝ) :
    isingZ m n J β = Matrix.trace (transferMatrix n J β ^ m) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = j + 1 :=
    ⟨m - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne m))).symm⟩
  rw [isingZ_eq_sum_prod]
  exact cyclic_sum_prod_eq_trace (transferMatrix n J β) j

/-! ## Main result -/

/-- **Onsager 2D Ising — formalized statement, transfer-matrix reduction, and the
infinite-temperature base case.**

The 2D square-lattice Ising model on the periodic `m × n` lattice is formalized above
(`isingEnergy`, `isingZ`, `isingLogZDensity`), and Onsager's exact free energy density is
`onsagerLogZDensity`; the full theorem is recorded as `OnsagerFreeEnergyStatement`.

This theorem collects what is proved here in Lean-checked form:

* the **transfer-matrix reduction**: at *every* temperature and for every lattice size,
  `Z = tr (T ^ m)` for the `2ⁿ × 2ⁿ` transfer matrix `T` — the identity on which Onsager's
  solution is built;
* the partition function of the `m × n` torus is exactly `2 ^ (m n)` at `β = 0`;
* Onsager's integral expression evaluates to `log 2` at `β = 0`;
* the finite-volume free energy density agrees with Onsager's expression at `β = 0`,
  for every lattice size; and consequently
* the limit asserted by `OnsagerFreeEnergyStatement` holds at `β = 0`. -/
