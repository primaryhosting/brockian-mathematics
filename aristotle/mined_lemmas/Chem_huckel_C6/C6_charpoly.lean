import Mathlib

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

/-
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Matrix Polynomial SimpleGraph

namespace Chem

/-- The adjacency matrix of the cycle graph `C₆` (the Hückel matrix of benzene,
with `α = 0`, `β = 1`). -/

lemma C6_charpoly :
    C6.charpoly = ∏ k : Fin 6, (X - C (2 * Real.cos (2 * Real.pi * k / 6))) := by
  set u : (Matrix (Fin 6) (Fin 6) ℝ)ˣ :=
    ⟨eigenBasis, eigenBasisInv, eigenBasis_mul_inv, inv_mul_eigenBasis⟩
  have hval : (↑u : Matrix (Fin 6) (Fin 6) ℝ) = eigenBasis := rfl
  have hinv : ((u⁻¹ : (Matrix (Fin 6) (Fin 6) ℝ)ˣ) : Matrix (Fin 6) (Fin 6) ℝ)
      = eigenBasisInv := rfl
  have h := Matrix.charpoly_units_conj u (diagonal spec)
  rw [hval, hinv, C6_conj] at h
  rw [h, Matrix.charpoly_diagonal]
  exact Finset.prod_congr rfl fun k _ => by rw [spec_eq_cos k]

/-- **Hückel theory for benzene (C₆).** The eigenvalues of the adjacency matrix of the
cycle graph `C₆` are exactly the numbers `2 cos (2πk/6)`, `k = 0, …, 5`; moreover the
characteristic polynomial factors as `∏ₖ (X - 2 cos (2πk/6))`, so these are the
eigenvalues with multiplicity. -/
