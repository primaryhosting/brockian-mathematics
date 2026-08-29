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

theorem multOp_essentiallySelfAdjoint (m : α → ℝ) (hm : Measurable m) :
    IsEssentiallySelfAdjoint (multDomain μ m) (multOp μ m) := by
  refine ⟨multDomain_dense m hm, multOp_symmetric m, ?_, ?_⟩
  · have hrange : (Set.range fun x : multDomain μ m =>
        multOp μ m x + Complex.I • (x : Lp ℂ 2 μ)) = Set.univ := by
      ext g
      simp only [Set.mem_range, Set.mem_univ, iff_true]
      obtain ⟨f, hf⟩ := multOp_add_surjective m hm 1 one_ne_zero g
      exact ⟨f, by simpa using hf⟩
    rw [hrange]
    exact dense_univ
  · have hrange : (Set.range fun x : multDomain μ m =>
        multOp μ m x - Complex.I • (x : Lp ℂ 2 μ)) = Set.univ := by
      ext g
      simp only [Set.mem_range, Set.mem_univ, iff_true]
      obtain ⟨f, hf⟩ := multOp_add_surjective m hm (-1) (by norm_num) g
      refine ⟨f, ?_⟩
      rw [← hf, sub_eq_add_neg, ← neg_smul]
      norm_num
    rw [hrange]
    exact dense_univ

end Mult

/-! ## The free Laplacian -/

section FreeLaplacian

variable (E : Type*) [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Fourier multiplier of the free Laplacian `-Δ`: with the normalisation
`𝓕 f (ξ) = ∫ e^{-2πi⟪x, ξ⟫} f x`, one has `𝓕 (-Δ f) (ξ) = 4π²‖ξ‖² 𝓕 f (ξ)`. -/
