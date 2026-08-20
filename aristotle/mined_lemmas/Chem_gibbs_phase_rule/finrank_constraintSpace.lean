import Mathlib
/-!
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
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

namespace Chem

/-! ## An affine dimension count for linear systems -/

/-- For a surjective linear map `f`, the solution set of `f v = b` is nonempty and its
direction (the vector span of the solution set) is exactly `ker f`. -/

theorem finrank_constraintSpace (C P : ℕ) :
    Module.finrank ℝ ((Fin P → ℝ) × (Fin (P - 1) → Fin C → ℝ)) = P + (P - 1) * C := by
  rw [Module.finrank_prod, finrank_matrix_space, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin]

/-! ## The Gibbs phase rule -/

/-- **Gibbs phase rule.**  Consider a system of `C` components distributed over `P ≥ 1`
phases.  Its intensive state is described by temperature, pressure and the mole fractions
`x j i` of component `i` in phase `j`.  The equilibrium conditions are:

* normalization: `∑ i, x j i = 1` for each phase `j`;
* equality of the chemical potentials of each component across the phases, encoded as a
  linear map `equil : PhaseState C P →ₗ[ℝ] (Fin (P-1) → Fin C → ℝ)`, giving `(P-1) * C`
  conditions.

Under the nondegeneracy hypothesis that these constraints are independent (the combined
constraint map is surjective), the set of equilibrium states is a nonempty affine subspace
whose dimension — the number `F` of degrees of freedom — satisfies `F + P = C + 2`,
i.e. `F = C - P + 2`. -/
