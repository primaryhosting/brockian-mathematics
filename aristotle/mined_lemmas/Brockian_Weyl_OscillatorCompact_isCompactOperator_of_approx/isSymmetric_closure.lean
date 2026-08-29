/-
  CompactCriterion.lean — an abstract compactness criterion: an operator whose
  unit-ball image is uniformly approximable by finite-dimensional subspaces is
  a compact operator.
-/
import Mathlib

open Metric Filter

namespace Brockian.Weyl.OscillatorCompact

/-- An operator whose closed-unit-ball image is uniformly approximable by
finite-dimensional subspaces is a compact operator. -/

theorem isSymmetric_closure {T : H →ₗ.[ℂ] H} (hsym : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) : IsSymmetric T.closure := by
  have hcl := isClosable_of_isSymmetric hsym hd
  have hle := closure_le_adjoint hsym hd
  have hfa := LinearPMap.adjoint_isFormalAdjoint (T := T) hd
  intro x y
  obtain ⟨u, hu1, hu2⟩ := exists_seq_tendsto_closure hcl y
  have hx : (x : H) ∈ T.adjoint.domain := hle.1 x.2
  have hxval : T.closure x = T.adjoint ⟨(x : H), hx⟩ := hle.2 rfl
  have hkey : ∀ n, ⟪T.closure x, ((u n : H))⟫_ℂ = ⟪(x : H), T (u n)⟫_ℂ := by
    intro n
    rw [hxval]
    exact hfa ⟨(x : H), hx⟩ (u n)
  have hlim1 : Tendsto (fun n => ⟪T.closure x, ((u n : H))⟫_ℂ) atTop
      (𝓝 ⟪T.closure x, (y : H)⟫_ℂ) :=
    (continuous_inner (𝕜 := ℂ)).continuousAt.tendsto.comp
      (Filter.Tendsto.prodMk_nhds tendsto_const_nhds hu1)
  have hlim2 : Tendsto (fun n => ⟪(x : H), T (u n)⟫_ℂ) atTop
      (𝓝 ⟪(x : H), T.closure y⟫_ℂ) :=
    (continuous_inner (𝕜 := ℂ)).continuousAt.tendsto.comp
      (Filter.Tendsto.prodMk_nhds tendsto_const_nhds hu2)
  have hlim3 : Tendsto (fun n => ⟪T.closure x, ((u n : H))⟫_ℂ) atTop
      (𝓝 ⟪(x : H), T.closure y⟫_ℂ) := by
    simpa only [hkey] using hlim2
  exact tendsto_nhds_unique hlim1 hlim3

/-! ### Orthogonality of the shifted range and the deficiency spaces -/

/-- If `g` is orthogonal to the range of `T - z`, then `g` lies in the
deficiency space of `T` at `conj z`. -/
