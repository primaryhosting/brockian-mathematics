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
# The basic criterion for essential self-adjointness

This file develops the abstract operator-theoretic input for `Brockian.Weyl.FreeLaplacian2`:
a densely defined symmetric operator on a complex Hilbert space whose two deficiency ranges
`Ran (T + i)` and `Ran (T - i)` are dense has self-adjoint closure, i.e. it is
*essentially self-adjoint*.
-/

namespace Brockian.Weyl

open LinearPMap Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The operator `x ↦ T x + z • x` on the domain of `T`. -/

theorem isSelfAdjoint_closure_of_dense_defRange {T : H →ₗ.[ℂ] H}
    (hdom : Dense (T.domain : Set H)) (hsymm : T.IsFormalAdjoint T)
    (hplus : Dense (defRange T Complex.I : Set H))
    (hminus : Dense (defRange T (-Complex.I) : Set H)) :
    IsSelfAdjoint T.closure := by
  have hIre : (Complex.I).re = 0 := by simp
  have hInorm : ‖Complex.I‖ = 1 := by simp
  have htop : defRange T.closure Complex.I = ⊤ :=
    defRange_closure_eq_top hdom hsymm hIre hInorm hplus
  have hCle : T.closure ≤ T† := closure_le_adjoint hdom hsymm
  -- every element of the domain of the adjoint lies in the domain of the closure
  have key : ∀ (v : H) (hv : v ∈ (T†).domain),
      ∃ u : T.closure.domain, (u : H) = v ∧ T† ⟨v, hv⟩ = T.closure u := by
    intro v hv
    obtain ⟨u, hu⟩ : ∃ u : T.closure.domain,
        T.closure u + Complex.I • (u : H) = T† ⟨v, hv⟩ + Complex.I • v := by
      have hmem : (T† ⟨v, hv⟩ + Complex.I • v) ∈ defRange T.closure Complex.I := by
        rw [htop]; trivial
      exact hmem
    have hgmem : v - (u : H) ∈ (T†).domain := Submodule.sub_mem _ hv (hCle.1 u.2)
    have hval : T† ⟨v - (u : H), hgmem⟩ = -Complex.I • (v - (u : H)) := by
      have h1 : T† ⟨v - (u : H), hgmem⟩ = T† ⟨v, hv⟩ - T† ⟨(u : H), hCle.1 u.2⟩ := by
        rw [← LinearPMap.map_sub]; rfl
      have h2 : T† ⟨(u : H), hCle.1 u.2⟩ = T.closure u := (hCle.2 rfl).symm
      have h3 : T† ⟨v, hv⟩ - T.closure u = Complex.I • (u : H) - Complex.I • v := by
        linear_combination (norm := module) -hu
      rw [h1, h2, h3, smul_sub]
      module
    have horth : ∀ w : defRange T (-Complex.I), inner ℂ (w : H) (v - (u : H)) = 0 := by
      rintro ⟨w, x, rfl⟩
      have hIF := LinearPMap.adjoint_isFormalAdjoint hdom ⟨v - (u : H), hgmem⟩ x
      rw [hval] at hIF
      have hzero : inner ℂ (v - (u : H)) (T x + (-Complex.I) • (x : H)) = 0 := by
        rw [inner_add_right, inner_smul_right, ← hIF, inner_smul_left]
        simp [Complex.conj_I]
      rw [← inner_conj_symm]
      simp only [defOp_apply] at hzero ⊢
      rw [hzero]
      simp
    have hg : v - (u : H) = 0 := Dense.eq_zero_of_inner_right hminus horth
    have hvu : (u : H) = v := by
      have := sub_eq_zero.mp hg
      exact this.symm
    refine ⟨u, hvu, ?_⟩
    have : T† ⟨v, hv⟩ + Complex.I • v = T.closure u + Complex.I • v := by
      rw [← hu, hvu]
    exact add_right_cancel this
  have hadj_le : T† ≤ T.closure := by
    constructor
    · intro v hv
      obtain ⟨u, hu1, -⟩ := key v hv
      rw [← hu1]
      exact u.2
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      obtain ⟨u, hu1, hu2⟩ := key x hx
      have : u = ⟨y, hy⟩ := Subtype.ext (by rw [hu1]; exact hxy)
      rw [hu2, this]
  have heq : T† = T.closure := le_antisymm hadj_le hCle
  rw [LinearPMap.isSelfAdjoint_def, adjoint_closure_eq hdom hsymm, heq]

end Brockian.Weyl

/-
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import Brockian.Weyl.EssentialSelfAdjoint

/-!
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.Weyl.FreeLaplacian2

open MeasureTheory SchwartzMap Complex FourierTransform Laplacian LineDeriv
open scoped Real ContDiff

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### The Fourier transform of the Laplacian -/

variable {V}

/-- The Fourier transform turns a directional derivative into multiplication. -/
