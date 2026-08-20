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

import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate Real
open LinearPMap Submodule

namespace Brockian.Weyl.SchrodingerMinimal

/-! ## Essential self-adjointness -/

section Abstract

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A densely defined operator `A` is *essentially self-adjoint* when it is symmetric and its
adjoint is self-adjoint (equivalently, its closure is self-adjoint; equivalently, it has a
unique self-adjoint extension, see `unique_selfAdjoint_extension`). -/

theorem repr_adjoint (u : (diagMin b lam).adjoint.domain) (i : ι) :
    b.repr ((diagMin b lam).adjoint u) i = (lam i : ℂ) * b.repr u i := by
  have h := LinearPMap.adjoint_isFormalAdjoint (T := diagMin b lam) (diagMin_dense b lam)
      u ⟨b i, basis_mem_domain b lam i⟩
  rw [diagMin_apply_basis, inner_smul_right] at h
  have h' := congrArg (starRingEnd ℂ) h
  simp only [map_mul, Complex.conj_ofReal, inner_conj_symm] at h'
  rw [b.repr_apply_apply, b.repr_apply_apply, h']

omit [CompleteSpace E] in
/-- Two vectors whose Fourier coefficients are multiplied by the *real* sequence `lam` can be
swapped inside an inner product. -/
