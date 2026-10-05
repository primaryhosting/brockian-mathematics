/-
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open MeasureTheory ProbabilityTheory

namespace Frontier

/-- The standard Gaussian measure on `ℝ^n`, defined as the `n`-fold product of the
standard Gaussian measure on `ℝ`. -/

theorem symmetric_convex_subsets_nested_dim_one (K L : Set (Fin 1 → ℝ))
    (hK : Convex ℝ K) (hL : Convex ℝ L) (hKs : IsSymmetric K) (hLs : IsSymmetric L) :
    K ⊆ L ∨ L ⊆ K := by
  set e : (Fin 1 → ℝ) ≃ₗ[ℝ] ℝ := LinearEquiv.funUnique (Fin 1) ℝ ℝ with he
  have himg : ∀ (A : Set (Fin 1 → ℝ)), Convex ℝ A → Convex ℝ (⇑e '' A) := by
    intro A hA
    exact hA.linear_image (e : (Fin 1 → ℝ) →ₗ[ℝ] ℝ)
  have hsym : ∀ (A : Set (Fin 1 → ℝ)), IsSymmetric A → ∀ x ∈ ⇑e '' A, -x ∈ ⇑e '' A := by
    intro A hA x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨-y, hA y hy, by simp⟩
  have hinj : ∀ (A B : Set (Fin 1 → ℝ)), ⇑e '' A ⊆ ⇑e '' B → A ⊆ B := by
    intro A B h
    have := Set.preimage_mono (f := ⇑e) h
    rwa [Set.preimage_image_eq _ e.injective, Set.preimage_image_eq _ e.injective] at this
  rcases symmetric_convex_subsets_nested (⇑e '' K) (⇑e '' L) (himg K hK) (himg L hL)
      (hsym K hKs) (hsym L hLs) with h | h
  · exact Or.inl (hinj K L h)
  · exact Or.inr (hinj L K h)

/-- **Gaussian correlation inequality, one-dimensional base case.**
For any two symmetric convex subsets `K`, `L` of `ℝ¹`, the standard Gaussian measure `γ`
satisfies `γ(K) * γ(L) ≤ γ(K ∩ L)`. -/
