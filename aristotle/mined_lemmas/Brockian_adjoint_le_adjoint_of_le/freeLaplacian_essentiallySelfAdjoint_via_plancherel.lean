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
# A basic criterion for essential self-adjointness

This file develops, from scratch, the classical criterion of von Neumann:

If `A` is a densely defined symmetric operator on a complex Hilbert space `H` such that the
ranges of `A + i` and `A - i` are dense — stated here in the equivalent form that a vector
orthogonal to such a range vanishes — then the adjoint `A†` is self-adjoint.  This is exactly
the statement that `A` is *essentially self-adjoint*: the closure of `A` (which is `A††`) is
self-adjoint, equivalently `A` has a unique self-adjoint extension, namely `A†`.

## Main results

* `Brockian.isSelfAdjoint_adjoint_of_denseRange`: the criterion.
* `Brockian.eq_adjoint_of_isSelfAdjoint_of_le`: uniqueness of the self-adjoint extension.
-/

open scoped ComplexInnerProductSpace
open LinearPMap

noncomputable section

namespace Brockian

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Antitonicity of the adjoint: an extension has a smaller adjoint. -/

theorem freeLaplacian_essentiallySelfAdjoint_via_plancherel (d : ℕ) :
    Dense ((freeLaplacianPMap d).domain : Set (L2s d)) ∧
      freeLaplacianPMap d ≤ (freeLaplacianPMap d).adjoint ∧
        IsSelfAdjoint (freeLaplacianPMap d).adjoint ∧
          ∀ B : L2s d →ₗ.[ℂ] L2s d, IsSelfAdjoint B → freeLaplacianPMap d ≤ B →
            B = (freeLaplacianPMap d).adjoint := by
  have hdense := dense_domain d
  have hsym := freeLaplacian_symmetric d
  have hshift : ∀ z : ℂ, z.im ≠ 0 → ∀ u : L2s d,
      (∀ x : (freeLaplacianPMap d).domain,
        ⟪u, freeLaplacianPMap d x + z • (x : L2s d)⟫ = 0) → u = 0 := by
    intro z hz u hu
    refine eq_zero_of_orthogonal_range d z hz u fun f => ?_
    have hx := hu ⟨schwartzToL2 d f, mem_freeLaplacianPMap_domain d f⟩
    rwa [freeLaplacianPMap_apply d ⟨schwartzToL2 d f, mem_freeLaplacianPMap_domain d f⟩ f rfl]
      at hx
  have hesa : IsSelfAdjoint (freeLaplacianPMap d).adjoint :=
    Brockian.isSelfAdjoint_adjoint_of_denseRange hdense hsym
      (hshift Complex.I (by simp))
      (by
        intro u hu
        refine hshift (-Complex.I) (by simp) u fun x => ?_
        have := hu x
        rw [← this]
        congr 1
        module)
  exact ⟨hdense, Brockian.symmetric_le_adjoint hdense hsym, hesa,
    fun B hB hAB => Brockian.eq_adjoint_of_isSelfAdjoint_of_le hdense hesa hB hAB⟩

end Brockian.FreeLaplacianPlancherel

