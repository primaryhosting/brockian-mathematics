/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not allow a module docstring before the import commands, so the required
header appears here as an ordinary block comment; the text is otherwise verbatim.)
-/

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

namespace Chem

open Complex Polynomial Matrix SimpleGraph

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₁₆`, i.e. the Hückel matrix of
cyclic C₁₆ in units where the Coulomb integral is `0` and the resonance integral is `1`. -/

theorem C16Adj_charpoly :
    C16Adj.charpoly = ∏ k : Fin 16, (X - C ((huckelEigval k : ℂ))) := by
  let M : (Matrix (Fin 16) (Fin 16) ℂ)ˣ := ⟨Umat, Vmat, Umat_mul_Vmat, Vmat_mul_Umat⟩
  have hconj : ((M : Matrix (Fin 16) (Fin 16) ℂ) * Dmat * (↑M⁻¹ : Matrix (Fin 16) (Fin 16) ℂ)
      ).charpoly = Dmat.charpoly := Matrix.charpoly_units_conj M Dmat
  have hM : (M : Matrix (Fin 16) (Fin 16) ℂ) = Umat := rfl
  have hMinv : (↑M⁻¹ : Matrix (Fin 16) (Fin 16) ℂ) = Vmat := rfl
  rw [hM, hMinv] at hconj
  rw [C16Adj_eq_conj, hconj, Dmat, Matrix.charpoly_diagonal]

/-- **Hückel theory for cyclic C₁₆.**  The adjacency (Hückel) matrix of the cycle graph `C₁₆`
has characteristic polynomial `∏_{k=0}^{15} (X - 2 cos (2πk/16))`, and hence its spectrum,
i.e. its set of eigenvalues, is exactly `{2 cos (2πk/16) : k = 0, …, 15}`. -/
