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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

/-!
# Hückel spectrum of the cycle `C₁₉`

We compute the spectrum of the adjacency matrix of Mathlib's cycle graph on `19` vertices
(the Hückel matrix of the annulene `C₁₉H₁₉`, with `α = 0`, `β = 1`), showing it is exactly
the set of numbers `2 * cos (2 π k / 19)` for `k = 0, …, 18`.

The vertex type `Fin 19` of `SimpleGraph.cycleGraph 19` is definitionally `ZMod 19`, and we
freely work with the ring structure of `ZMod 19` on it.  The eigenvectors are the additive
characters `j ↦ e (j * k)`, assembled into the discrete Fourier matrix `Chem.dftMatrix`.
-/

/-- The adjacency matrix of the cycle graph `C₁₉`, i.e. the Hückel matrix of `C₁₉H₁₉`
(with Coulomb integral `α = 0` and resonance integral `β = 1`). -/

lemma spectrum_diagonal {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℂ) :
    spectrum ℂ (Matrix.diagonal d) = Set.range d := by
  ext μ
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, Matrix.algebraMap_eq_diagonal,
    show ((algebraMap ℂ (n → ℂ)) μ) = (fun _ => μ) from rfl, Matrix.diagonal_sub,
    Matrix.det_diagonal, isUnit_iff_ne_zero, not_ne_iff, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero, eq_comm]

/-- **Hückel spectrum of the cycle `C₁₉`.**  The eigenvalues of the adjacency matrix of the
cycle graph on `19` vertices are exactly the numbers `2 cos (2 π k / 19)` for `k = 0, …, 18`. -/
