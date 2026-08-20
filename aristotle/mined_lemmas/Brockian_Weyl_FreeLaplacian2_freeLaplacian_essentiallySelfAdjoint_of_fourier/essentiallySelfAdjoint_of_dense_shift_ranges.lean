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
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

-- Note: Lean requires `import` commands to come before any module docstring `/-! ... -/`, so the
-- required header appears verbatim at the very top of the file as a block comment and is repeated
-- here, after the import, as the module docstring.

/-!
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
The free Laplacian `-Δ`, defined on the Schwartz space `𝓢(ℝ^d, ℂ)` regarded as a dense
subspace of `L²(ℝ^d, ℂ)`, is essentially self-adjoint.

The proof follows the classical "basic criterion" of von Neumann/Weyl:

* an abstract criterion (`essentiallySelfAdjoint_of_dense_shift_ranges`): a densely defined
  symmetric operator whose deficiency ranges `Ran (T ± i)` are dense is essentially
  self-adjoint;
* the Fourier transform turns `-Δ` on Schwartz space into multiplication by
  `ξ ↦ 4π²‖ξ‖²` (`fourier_negLaplacianS`), and dividing a smooth compactly supported
  function by `4π²‖ξ‖² ± i` (which never vanishes) produces again a smooth compactly
  supported function.  Since smooth compactly supported functions are dense in `L²` and
  the Fourier transform is unitary on `L²` (Plancherel), the deficiency ranges are dense.
-/

open MeasureTheory SchwartzMap Filter LinearPMap
open scoped FourierTransform ComplexInnerProductSpace LinearPMap Laplacian LineDeriv Topology
  ContDiff

noncomputable section

namespace Brockian.Weyl.FreeLaplacian2

/-! ## An abstract criterion for essential self-adjointness -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The operator `T + c` on the domain of the partially defined operator `T`. -/

theorem essentiallySelfAdjoint_of_dense_shift_ranges {T : E →ₗ.[ℂ] E}
    (hT : Dense (T.domain : Set E)) (hsym : T.IsFormalAdjoint T)
    (hplus : Dense ((LinearMap.range (shiftMap T Complex.I) : Submodule ℂ E) : Set E))
    (hminus : Dense ((LinearMap.range (shiftMap T (-Complex.I)) : Submodule ℂ E) : Set E)) :
    EssentiallySelfAdjoint T := by
  have hT' : Dense ((T†).domain : Set E) := dense_adjoint_domain hT hsym
  have h1 : T†† ≤ T† := adjoint_adjoint_le hT hsym
  have hTle2 : T ≤ T†† :=
    LinearPMap.IsFormalAdjoint.le_adjoint hT' (LinearPMap.adjoint_isFormalAdjoint hT)
  have hsub : closure (T.graph : Set (E × E)) ⊆ ((T††).graph : Set (E × E)) := by
    refine (LinearPMap.adjoint_isClosed hT').closure_subset_iff.mpr ?_
    exact_mod_cast LinearPMap.le_graph_of_le hTle2
  have key : ∀ y : (T†).domain, ∃ h : (y : E) ∈ (T††).domain, T†† ⟨(y : E), h⟩ = T† y := by
    intro y
    obtain ⟨p, hp, hpu⟩ := exists_mem_closure_graph hsym (c := -Complex.I) (by simp) (by simp)
      hminus (T† y + (-Complex.I) • (y : E))
    have hpg : p ∈ (T††).graph := hsub hp
    rw [LinearPMap.mem_graph_iff] at hpg
    obtain ⟨z, hz1, hz2⟩ := hpg
    have hz1' : (z : E) ∈ (T†).domain := h1.1 z.2
    have hz2' : T† ⟨(z : E), hz1'⟩ = p.2 := by
      rw [← hz2]; exact (h1.2 rfl).symm
    have hwval : T† (y - (⟨(z : E), hz1'⟩ : (T†).domain)) = Complex.I • ((y : E) - (z : E)) := by
      rw [LinearPMap.map_sub, hz2', hz1]
      have hp2 : p.2 = T† y + (-Complex.I) • (y : E) - (-Complex.I) • p.1 := by
        rw [← hpu]; module
      rw [hp2]
      module
    have hzero : ((y - (⟨(z : E), hz1'⟩ : (T†).domain) : (T†).domain) : E) = 0 := by
      refine eq_zero_of_dense_shift_range hT hplus _ ?_
      rw [hwval]
      simp only [Submodule.coe_sub]
      simp
    simp only [Submodule.coe_sub] at hzero
    have hyz : (y : E) = (z : E) := sub_eq_zero.mp hzero
    refine ⟨by rw [hyz]; exact z.2, ?_⟩
    have hzz : (⟨(y : E), by rw [hyz]; exact z.2⟩ : (T††).domain) = z := by
      ext; exact hyz
    rw [hzz, hz2, ← hz2']
    congr 1
    ext
    exact hyz.symm
  have h2 : T† ≤ T†† := by
    refine ⟨fun y hy => (key ⟨y, hy⟩).1, ?_⟩
    rintro ⟨y, hy⟩ ⟨y', hy'⟩ h
    simp only at h
    subst h
    exact ((key ⟨y, hy⟩).2).symm
  exact le_antisymm h1 h2

end Abstract

/-! ## The free Laplacian on `L²(ℝ^d)` -/

/-- Euclidean space `ℝ^d`. -/
abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Hilbert space `L²(ℝ^d, ℂ)`. -/
abbrev L2 (d : ℕ) := Lp (α := Euc d) ℂ 2 volume

variable (d : ℕ)

/-- The inclusion of Schwartz functions into `L²`. -/
