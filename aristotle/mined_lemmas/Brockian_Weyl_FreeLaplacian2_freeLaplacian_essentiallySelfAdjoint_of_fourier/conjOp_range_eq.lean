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
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex ComplexInnerProductSpace FourierTransform

noncomputable section

namespace Brockian.Weyl.FreeLaplacian2

/-! ## Essential self-adjointness -/

/-- A (densely defined) operator `T` with domain `D` inside a complex inner product space `H`
is *essentially self-adjoint* when it is densely defined, symmetric, and the ranges of
`T + i` and `T - i` are dense (the basic criterion for essential self-adjointness of a
symmetric operator). -/

lemma conjOp_range_eq (U : H ≃ₗᵢ[ℂ] H') (D : Submodule ℂ H') (T : D →ₗ[ℂ] H') (c : ℂ) :
    (Set.range fun x : conjDomain U D => conjOp U D T x + c • (x : H)) =
      U ⁻¹' (Set.range fun y : D => T y + c • (y : H')) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨U x, x.2⟩, ?_⟩
    show T ⟨U x, x.2⟩ + c • ((⟨U x, x.2⟩ : D) : H') = U (conjOp U D T x + c • (x : H))
    rw [map_add, map_smul, conjOp_apply, U.apply_symm_apply]
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := exists_conj_preimage U D y
    refine ⟨x, ?_⟩
    apply U.injective
    have hUx : U (x : H) = (y : H') := congrArg Subtype.val hx
    rw [map_add, map_smul, conjOp_apply, U.apply_symm_apply, hx, hUx]
    exact hy

/-- Essential self-adjointness is preserved by conjugation by a unitary. -/
