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
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Contents

The first part of this file develops the abstract von Neumann / Weyl deficiency criterion for
essential self-adjointness of a densely defined symmetric operator on a complex Hilbert space.

The second part constructs the minimal Schrödinger operator `-d²/dx² + V` on `L²(ℝ)`, with domain
the smooth compactly supported functions, and shows that it is essentially self-adjoint as soon as
the differential equation `-u'' + V u = ± i u` has no nonzero solution in `L²(ℝ)` (understood in
the distributional sense).
-/

namespace Brockian.Weyl

open LinearPMap Complex

section Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- A partially defined operator `T` on a complex inner product space is *symmetric* if
`⟪T x, y⟫ = ⟪x, T y⟫` for all `x, y` in its domain. -/

theorem isClosed_range_shiftMap {A : E →ₗ.[ℂ] E} (hA : A.IsClosed) (hs : IsSymmetricPMap A)
    {c : ℝ} (hc : c ≠ 0) : IsClosed ((LinearMap.range (shiftMap A c) : Submodule ℂ E) : Set E) := by
  haveI : CompleteSpace A.graph := hA.completeSpace_coe
  let Φ : A.graph →ₗ[ℂ] E :=
    { toFun := fun z => (z : E × E).2 + ((c : ℂ) * Complex.I) • (z : E × E).1
      map_add' := by
        intro a b
        simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add, smul_add]
        abel
      map_smul' := by
        intro r a
        simp only [Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply,
          smul_add, smul_comm r ((c : ℂ) * Complex.I)] }
  have hΦapply : ∀ z : A.graph, Φ z = (z : E × E).2 + ((c : ℂ) * Complex.I) • (z : E × E).1 :=
    fun _ => rfl
  have hΦcont : Continuous Φ := by
    show Continuous fun z : A.graph => (z : E × E).2 + ((c : ℂ) * Complex.I) • (z : E × E).1
    fun_prop
  set ΦL : A.graph →L[ℂ] E := ⟨Φ, hΦcont⟩ with hΦL
  have hrange : Set.range ΦL = ((LinearMap.range (shiftMap A c) : Submodule ℂ E) : Set E) := by
    ext v
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨x, hx⟩ := (A.mem_graph_iff).mp z.2
      refine ⟨x, ?_⟩
      show A x + ((c : ℂ) * Complex.I) • (x : E)
          = (z : E × E).2 + ((c : ℂ) * Complex.I) • (z : E × E).1
      rw [hx.1, hx.2]
    · rintro ⟨x, rfl⟩
      exact ⟨⟨((x : E), A x), A.mem_graph x⟩, rfl⟩
  rw [← hrange]
  have hbound : ∀ z : A.graph, ‖z‖ ≤ (max 1 |c|⁻¹) * ‖ΦL z‖ := by
    intro z
    obtain ⟨x, hx⟩ := (A.mem_graph_iff).mp z.2
    have hz1 : (z : E × E).1 = (x : E) := hx.1.symm
    have hz2 : (z : E × E).2 = A x := hx.2.symm
    have hΦz : ΦL z = shiftMap A c x := by
      show (z : E × E).2 + ((c : ℂ) * Complex.I) • (z : E × E).1 = _
      rw [hz1, hz2, shiftMap_apply]
    have hnormsq : ‖ΦL z‖ ^ 2 = ‖A x‖ ^ 2 + c ^ 2 * ‖(x : E)‖ ^ 2 := by
      rw [hΦz]; exact norm_shiftMap_sq hs c x
    have hx1 : ‖(x : E)‖ ≤ |c|⁻¹ * ‖ΦL z‖ := by
      rw [inv_mul_eq_div, le_div_iff₀ (abs_pos.mpr hc)]
      nlinarith [norm_nonneg (ΦL z), norm_nonneg ((x : E)), norm_nonneg (A x), sq_abs c,
        abs_nonneg c]
    have hx2 : ‖A x‖ ≤ ‖ΦL z‖ := by
      nlinarith [norm_nonneg (ΦL z), norm_nonneg (A x), norm_nonneg ((x : E)), sq_nonneg c,
        sq_nonneg (‖(x : E)‖)]
    have hnz : ‖z‖ = max ‖(z : E × E).1‖ ‖(z : E × E).2‖ := by
      rw [← Prod.norm_def]; rfl
    rw [hnz, hz1, hz2]
    have h1 : ‖(x : E)‖ ≤ max 1 |c|⁻¹ * ‖ΦL z‖ := by
      refine hx1.trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    have h2 : ‖A x‖ ≤ max 1 |c|⁻¹ * ‖ΦL z‖ := by
      refine hx2.trans ?_
      nlinarith [norm_nonneg (ΦL z), le_max_left (1 : ℝ) |c|⁻¹]
    exact max_le h1 h2
  have hK : (Real.toNNReal (max 1 |c|⁻¹) : ℝ) = max 1 |c|⁻¹ :=
    Real.coe_toNNReal _ (le_trans zero_le_one (le_max_left _ _))
  have hanti : AntilipschitzWith (Real.toNNReal (max 1 |c|⁻¹)) ΦL := by
    refine ContinuousLinearMap.antilipschitz_of_bound ΦL ?_
    intro z
    rw [hK]
    exact hbound z
  exact hanti.isClosed_range ΦL.uniformContinuous

/-- If `w` is orthogonal to the range of `T + c i` then `w` is an eigenvector of the adjoint
with eigenvalue `c i`. -/
