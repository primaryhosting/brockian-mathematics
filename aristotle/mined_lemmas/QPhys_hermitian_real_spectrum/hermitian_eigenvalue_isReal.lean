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

theorem hermitian_eigenvalue_isReal
    (T : E →ₗ[ℂ] E) (hT : ∀ x y : E, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue T μ) :
    ∃ r : ℝ, μ = (r : ℂ) := by
  obtain ⟨v, hv, hv0⟩ := hμ.exists_hasEigenvector
  refine ⟨μ.re, ?_⟩
  have him : μ.im = 0 :=
    hermitian_real_spectrum T hT μ v hv0 (by simpa using hv)
  exact Complex.ext rfl (by simpa using him)

end QPhys

