/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
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

open Polynomial

/-- The Hückel (adjacency) matrix of the cycle graph `C₃`: the π-system connectivity
matrix of a three-membered carbon ring, in units where the Coulomb integral is `α = 0`
and the resonance integral is `β = 1`. -/

lemma eigen_iff_det (A : Matrix (Fin 3) (Fin 3) ℝ) (μ : ℝ) :
    (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ A.mulVec v = μ • v) ↔
      (Matrix.scalar (Fin 3) μ - A).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, hAv⟩
    exact ⟨v, hv, by rw [Matrix.sub_mulVec, hAv, scalar_mulVec, sub_self]⟩
  · rintro ⟨v, hv, hAv⟩
    rw [Matrix.sub_mulVec, sub_eq_zero, scalar_mulVec] at hAv
    exact ⟨v, hv, hAv.symm⟩

/--
**Hückel theory for the cyclopropenyl π-system (`C₃`).**

The adjacency (Hückel) matrix of the cycle graph `C₃` has characteristic polynomial
`∏_{k=0}^{2} (X - 2cos(2πk/3))`, and a real number `μ` is an eigenvalue of that matrix
precisely when `μ = 2cos(2πk/3)` for some `k ∈ {0, 1, 2}`.

Numerically the spectrum is `{2, -1, -1}`: one bonding level at `α + 2β` and a doubly
degenerate antibonding level at `α - β`.
-/
