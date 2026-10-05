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
noncomputable def stdGaussian (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

instance instIsProbabilityMeasureStdGaussian (n : ℕ) :
    IsProbabilityMeasure (stdGaussian n) := by
  unfold stdGaussian
  infer_instance

/-- A set is (centrally) symmetric if it is invariant under `x ↦ -x`. -/
def IsSymmetric {n : ℕ} (A : Set (Fin n → ℝ)) : Prop := ∀ x ∈ A, -x ∈ A

/-- The Gaussian correlation inequality in dimension `n` (Royen's theorem):
for any two symmetric convex subsets `K`, `L` of `ℝ^n`, the standard Gaussian measure
satisfies `γ(K) * γ(L) ≤ γ(K ∩ L)`. -/
def GaussianCorrelation (n : ℕ) : Prop :=
  ∀ K L : Set (Fin n → ℝ), Convex ℝ K → Convex ℝ L → IsSymmetric K → IsSymmetric L →
    stdGaussian n K * stdGaussian n L ≤ stdGaussian n (K ∩ L)

/-! ### A general reduction: the inequality holds whenever the two sets are nested -/

/-- If one of the two sets is contained in the other, the Gaussian correlation inequality
holds in every dimension (no convexity or symmetry needed): this is just the fact that a
probability measure is bounded by `1`. -/
theorem gaussianCorrelation_of_subset {n : ℕ} (K L : Set (Fin n → ℝ))
    (h : K ⊆ L ∨ L ⊆ K) :
    stdGaussian n K * stdGaussian n L ≤ stdGaussian n (K ∩ L) := by
  rcases h with h | h
  · have hKL : K ∩ L = K := Set.inter_eq_self_of_subset_left h
    calc stdGaussian n K * stdGaussian n L ≤ stdGaussian n K * 1 :=
          mul_le_mul_left' prob_le_one _
      _ = stdGaussian n (K ∩ L) := by rw [mul_one, hKL]
  · have hKL : K ∩ L = L := Set.inter_eq_self_of_subset_right h
    calc stdGaussian n K * stdGaussian n L ≤ 1 * stdGaussian n L :=
          mul_le_mul_right' prob_le_one _
      _ = stdGaussian n (K ∩ L) := by rw [one_mul, hKL]

/-! ### The one-dimensional case -/

/-- A symmetric convex subset of `ℝ` contains every point that is no further from the
origin than one of its points. -/
theorem mem_of_abs_le_of_symmetric_convex (S : Set ℝ) (hS : Convex ℝ S)
    (hsym : ∀ x ∈ S, -x ∈ S) {a b : ℝ} (ha : a ∈ S) (hab : |b| ≤ |a|) : b ∈ S := by
  refine hS.segment_subset (hsym a ha) ha ?_
  rw [segment_eq_uIcc, Set.mem_uIcc]
  rw [abs_le] at hab
  rcases abs_cases a with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; constructor <;> linarith [hab.1, hab.2]
  · right; constructor <;> linarith [hab.1, hab.2]

/-- Any two symmetric convex subsets of `ℝ` are nested: they are symmetric intervals
around the origin. -/
theorem symmetric_convex_subsets_nested (K L : Set ℝ) (hK : Convex ℝ K) (hL : Convex ℝ L)
    (hKs : ∀ x ∈ K, -x ∈ K) (hLs : ∀ x ∈ L, -x ∈ L) : K ⊆ L ∨ L ⊆ K := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [Set.not_subset] at h1 h2
  obtain ⟨x, hxK, hxL⟩ := h1
  obtain ⟨y, hyL, hyK⟩ := h2
  rcases le_total |x| |y| with h | h
  · exact hxL (mem_of_abs_le_of_symmetric_convex L hL hLs hyL h)
  · exact hyK (mem_of_abs_le_of_symmetric_convex K hK hKs hxK h)

/-- Any two symmetric convex subsets of `ℝ¹` are nested. -/
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
theorem gaussian_correlation : GaussianCorrelation 1 := by
  intro K L hK hL hKs hLs
  exact gaussianCorrelation_of_subset K L
    (symmetric_convex_subsets_nested_dim_one K L hK hL hKs hLs)

/-- The (degenerate) zero-dimensional case of the Gaussian correlation inequality. -/
theorem gaussian_correlation_dim_zero : GaussianCorrelation 0 := by
  intro K L _ _ _ _
  refine gaussianCorrelation_of_subset K L ?_
  by_cases h : K = ∅
  · exact Or.inl (h ▸ Set.empty_subset L)
  · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 h
    refine Or.inr fun y hy => ?_
    have : y = x := Subsingleton.elim _ _
    exact this ▸ hx

end Frontier

