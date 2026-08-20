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

theorem isClosed_defRange {T : H →ₗ.[ℂ] H} (hclosed : T.IsClosed)
    (hsymm : T.IsFormalAdjoint T) {z : ℂ} (hz : z.re = 0) (hz1 : ‖z‖ = 1) :
    IsClosed (defRange T z : Set H) := by
  have hG : IsClosed (T.graph : Set (H × H)) := hclosed
  haveI : CompleteSpace (T.graph : Set (H × H)) := hG.completeSpace_coe
  set L : (H × H) →L[ℂ] H :=
    (ContinuousLinearMap.snd ℂ H H) + z • (ContinuousLinearMap.fst ℂ H H) with hL
  set f : (T.graph : Submodule ℂ (H × H)) →L[ℂ] H := L.comp T.graph.subtypeL with hf
  have hrange : Set.range f = (defRange T z : Set H) := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨x, hx1, hx2⟩ := LinearPMap.mem_graph_iff T |>.mp p.2
      exact ⟨x, by simp [hf, hL, ← hx1, ← hx2]⟩
    · rintro ⟨x, rfl⟩
      refine ⟨⟨((x : H), T x), T.mem_graph x⟩, ?_⟩
      simp [hf, hL]
  rw [← hrange]
  have hanti : AntilipschitzWith 1 f := by
    apply AddMonoidHomClass.antilipschitz_of_bound
    intro p
    obtain ⟨x, hx1, hx2⟩ := LinearPMap.mem_graph_iff T |>.mp p.2
    have hfp : f p = T x + z • (x : H) := by simp [hf, hL, ← hx1, ← hx2]
    have hkey : ‖f p‖ ^ 2 = ‖T x‖ ^ 2 + ‖(x : H)‖ ^ 2 := by
      rw [hfp, norm_add_smul_sq hsymm x z hz, hz1]; ring
    have hp : ‖(p : H × H)‖ = max ‖(x : H)‖ ‖T x‖ := by rw [Prod.norm_def, ← hx1, ← hx2]
    have h1 : ‖(x : H)‖ ≤ ‖f p‖ := by
      nlinarith [norm_nonneg (f p), norm_nonneg (x : H), norm_nonneg (T x)]
    have h2 : ‖T x‖ ≤ ‖f p‖ := by
      nlinarith [norm_nonneg (f p), norm_nonneg (x : H), norm_nonneg (T x)]
    have hpp : ‖p‖ = ‖(p : H × H)‖ := rfl
    simp only [NNReal.coe_one, one_mul, hpp, hp]
    exact max_le h1 h2
  exact hanti.isClosed_range (ContinuousLinearMap.uniformContinuous f)

/-- The closure of a symmetric densely defined operator is symmetric. -/
