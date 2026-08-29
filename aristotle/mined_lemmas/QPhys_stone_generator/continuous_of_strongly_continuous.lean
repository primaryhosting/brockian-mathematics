/-
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate

namespace QPhys

section Strong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- On a finite-dimensional space, strong continuity of a family of operators implies
continuity in the operator norm. -/

theorem continuous_of_strongly_continuous (U : ℝ → (E →L[ℂ] E))
    (hstrong : ∀ x, Continuous fun t => U t x) : Continuous U := by
  classical
  set b := Module.finBasis ℂ E with hb
  set Ψ : (Fin (Module.finrank ℂ E) → E) ≃ₗ[ℂ] (E →L[ℂ] E) :=
    (b.constr ℂ).trans LinearMap.toContinuousLinearMap with hΨ
  have hΨcont : Continuous Ψ :=
    LinearMap.continuous_of_finiteDimensional (Ψ : (Fin (Module.finrank ℂ E) → E) →ₗ[ℂ] (E →L[ℂ] E))
  have hUeq : U = fun t => Ψ (fun i => U t (b i)) := by
    funext t
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro i
    simp [hΨ]
  rw [hUeq]
  exact hΨcont.comp (continuous_pi fun i => hstrong (b i))

end Strong

section BanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- A norm-continuous one-parameter group in a Banach algebra has a bounded generator `B`:
`U` is differentiable and `U' t = U t * B`.

The generator is produced by the classical averaging trick: for small `s > 0` the element
`V s = ∫ t in 0..s, U t` is invertible (it is close to `s • 1`), and the group law turns
`U r` into `(V (r + s) - V r) * (V s)⁻¹`, which is differentiable in `r`. -/
