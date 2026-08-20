/-
/-!
# Hermitian Real Spectrum
Category: Quantum Physics
Target: QPhys.hermitian_real_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Hermitian Real Spectrum
Category: Quantum Physics
Target: QPhys.hermitian_real_spectrum
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

namespace QPhys

open scoped ComplexConjugate
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Key intermediate lemma.** For a Hermitian (symmetric) operator `T`, every diagonal
matrix element `⟪v, T v⟫` is a real number, i.e. it is fixed by complex conjugation. -/

theorem hermitian_diagonal_element_conj_eq
    (T : E →ₗ[ℂ] E) (hT : ∀ x y : E, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ) (v : E) :
    conj (⟪v, T v⟫_ℂ) = ⟪v, T v⟫_ℂ := by
  conv_rhs => rw [← hT v v]
  rw [inner_conj_symm]

/-- **Hermitian operators have real spectrum.**
If `T` is a Hermitian operator on a complex inner product space and `μ` is an eigenvalue of
`T` (with eigenvector `v ≠ 0`), then `μ` is real: its imaginary part vanishes. -/
