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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

/-- Index set of the intensive variables of a heterogeneous system with `C` components
distributed over `P` phases: the two field variables (temperature and pressure), encoded by
`Bool`, together with the mole fraction `x j i` of component `i` in phase `j`.
Hence there are `2 + P * C` variables. -/
abbrev VarIndex (C P : ℕ) : Type := Bool ⊕ (Fin P × Fin C)

/-- Index set of the equilibrium constraints: one normalization condition
`∑ i, x j i = 1` per phase `j` (that is `P` conditions), together with the equalities of
chemical potentials between consecutive phases, `μ i (j) = μ i (j+1)`, one for each component
`i` and each of the `P - 1` consecutive pairs of phases.
Hence there are `P + (P - 1) * C` constraints. -/
abbrev ConIndex (C P : ℕ) : Type := Fin P ⊕ (Fin (P - 1) × Fin C)

/-- The number of intensive variables is `2 + P * C`. -/

noncomputable def constraintMap (C P : ℕ)
    (mu : Fin P → Fin C → ((VarIndex C P → ℝ) →ₗ[ℝ] ℝ)) :
    (VarIndex C P → ℝ) →ₗ[ℝ] (ConIndex C P → ℝ) where
  toFun x := Sum.elim (fun j => ∑ i, x (Sum.inr (j, i)))
      (fun p => mu (phaseLo p.1) p.2 x - mu (phaseHi p.1) p.2 x)
  map_add' x y := by
    funext c
    cases c with
    | inl j => simp [Finset.sum_add_distrib]
    | inr p => simp; ring
  map_smul' c x := by
    funext d
    cases d with
    | inl j => simp [Finset.mul_sum]
    | inr p => simp; ring

/-- An auxiliary embedding: when `1 ≤ C` and `P ≤ C + 2` the `(P-1) * C` chemical-potential
constraints can be indexed injectively by variables other than the distinguished mole
fractions `x j 0`, one of which is reserved for each phase to absorb the normalization. -/
