import RequestProject.Kron

/-!
# Vectorization, the modular operator and relative entropy

We vectorize matrices, express the relative entropy `Tr ρ log ρ - Tr ρ log σ` as (minus) a
quadratic form of `log (σ ⊗ (ρ⁻¹)ᵀ)` at the vectorization of `√ρ`, and record the
variational ("completing the square") characterization of resolvent quadratic forms.
-/

open Matrix
open scoped Kronecker ComplexOrder BigOperators MatrixOrder

namespace QI

variable {n m N : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype N] [DecidableEq N]

/-! ### Vectorization -/

/-- Vectorization of a matrix: the vector of all its entries, indexed by pairs. -/

lemma cfc_log_kron {A : Matrix n n ℂ} {B : Matrix m m ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    cfc Real.log (A ⊗ₖ B) = (cfc Real.log A) ⊗ₖ (1 : Matrix m m ℂ)
      + (1 : Matrix n n ℂ) ⊗ₖ (cfc Real.log B) := by
  obtain ⟨U, a, hU, hU', hapos, hdA⟩ := exists_diagonalization_pos hA
  obtain ⟨V, b, hV, hV', hbpos, hdB⟩ := exists_diagonalization_pos hB
  have hWH : (U ⊗ₖ V)ᴴ = Uᴴ ⊗ₖ Vᴴ := Matrix.conjTranspose_kronecker U V
  have hW1 : (U ⊗ₖ V) * (U ⊗ₖ V)ᴴ = 1 := by
    rw [hWH, ← Matrix.mul_kronecker_mul, hU, hV, Matrix.one_kronecker_one]
  have hW2 : (U ⊗ₖ V)ᴴ * (U ⊗ₖ V) = 1 := by
    rw [hWH, ← Matrix.mul_kronecker_mul, hU', hV', Matrix.one_kronecker_one]
  have hkron : A ⊗ₖ B = (U ⊗ₖ V) * diagonal (fun p : n × m => ((a p.1 * b p.2 : ℝ) : ℂ))
      * (U ⊗ₖ V)ᴴ := by
    conv_lhs => rw [hdA, hdB]
    rw [hWH, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul,
      Matrix.diagonal_kronecker_diagonal]
    congr 2
    funext p
    simp
  rw [cfc_of_diagonalization (unitary_of_mul hW1 hW2) _ hkron Real.log]
  have hsplit : (fun p : n × m => ((Real.log (a p.1 * b p.2) : ℝ) : ℂ))
      = fun p : n × m => ((Real.log (a p.1) : ℝ) : ℂ) * 1 + 1 * ((Real.log (b p.2) : ℝ) : ℂ) := by
    funext p
    rw [Real.log_mul (hapos p.1).ne' (hbpos p.2).ne']
    push_cast
    ring
  rw [hsplit]
  have hdiag : diagonal (fun p : n × m =>
        ((Real.log (a p.1) : ℝ) : ℂ) * 1 + 1 * ((Real.log (b p.2) : ℝ) : ℂ))
      = diagonal (fun i => ((Real.log (a i) : ℝ) : ℂ)) ⊗ₖ (1 : Matrix m m ℂ)
        + (1 : Matrix n n ℂ) ⊗ₖ diagonal (fun j => ((Real.log (b j) : ℝ) : ℂ)) := by
    rw [show (1 : Matrix m m ℂ) = diagonal (fun _ : m => (1 : ℂ)) from by simp,
      show (1 : Matrix n n ℂ) = diagonal (fun _ : n => (1 : ℂ)) from by simp,
      Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_kronecker_diagonal, ← diagonal_add]
  rw [hdiag, Matrix.mul_add, Matrix.add_mul, hWH]
  congr 1
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, hV]
    congr 1
    exact (cfc_of_diagonalization (unitary_of_mul hU hU') a hdA Real.log).symm
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, hU]
    congr 1
    exact (cfc_of_diagonalization (unitary_of_mul hV hV') b hdB Real.log).symm

end QI

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

import RequestProject.Channel
/-!
# Data Processing
Category: Frontier Qi
Target: QI.data_processing
Statement: Quantum relative entropy is monotone under CPTP maps (data-processing inequality).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped Kronecker ComplexOrder BigOperators MatrixOrder

namespace QI

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype ι] [DecidableEq ι]

/-! ### The variational functional -/

/-- The functional whose supremum over `Z` is the resolvent quadratic form
`⟪√ρ, (Δ + t)⁻¹ √ρ⟫`. -/
