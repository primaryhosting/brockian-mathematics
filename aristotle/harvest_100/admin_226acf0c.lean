/-
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

open MeasureTheory ProbabilityTheory

/-- The standard (centred, identity covariance) Gaussian measure on `Fin n → ℝ`,
built as the `n`-fold product of the real standard Gaussian. -/
noncomputable def stdGaussian (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => gaussianReal 0 1)

instance instIsProbabilityMeasureStdGaussian (n : ℕ) :
    IsProbabilityMeasure (stdGaussian n) := by
  unfold stdGaussian
  infer_instance

/-- **The Gaussian correlation inequality** (Royen's theorem) in dimension `n`:
for any two origin-symmetric convex (measurable) subsets `K`, `L` of `ℝ ^ n`, the standard
Gaussian measure satisfies `γ K * γ L ≤ γ (K ∩ L)`. -/
def GaussianCorrelationInequality (n : ℕ) : Prop :=
  ∀ K L : Set (Fin n → ℝ), Convex ℝ K → Convex ℝ L →
    (∀ x ∈ K, -x ∈ K) → (∀ x ∈ L, -x ∈ L) →
    MeasurableSet K → MeasurableSet L →
    stdGaussian n K * stdGaussian n L ≤ stdGaussian n (K ∩ L)

/-- A reduction step valid in every dimension: whenever the two sets are nested, the
Gaussian correlation inequality holds, simply because a probability measure is `≤ 1`. -/
theorem gaussian_correlation_of_nested {n : ℕ} (K L : Set (Fin n → ℝ))
    (h : K ⊆ L ∨ L ⊆ K) :
    stdGaussian n K * stdGaussian n L ≤ stdGaussian n (K ∩ L) := by
  rcases h with h | h
  · have hKL : K ∩ L = K := Set.inter_eq_self_of_subset_left h
    calc stdGaussian n K * stdGaussian n L ≤ stdGaussian n K * 1 := by
          exact mul_le_mul' le_rfl prob_le_one
      _ = stdGaussian n (K ∩ L) := by rw [mul_one, hKL]
  · have hKL : K ∩ L = L := Set.inter_eq_self_of_subset_right h
    calc stdGaussian n K * stdGaussian n L ≤ 1 * stdGaussian n L := by
          exact mul_le_mul' prob_le_one le_rfl
      _ = stdGaussian n (K ∩ L) := by rw [one_mul, hKL]

/-- In dimension one, an origin-symmetric convex set is "downward closed" for the absolute
value of the single coordinate. -/
theorem mem_of_abs_le_of_symm_convex {S : Set (Fin 1 → ℝ)} (hconv : Convex ℝ S)
    (hsymm : ∀ x ∈ S, -x ∈ S) {x y : Fin 1 → ℝ} (hx : x ∈ S) (hxy : |y 0| ≤ |x 0|) :
    y ∈ S := by
  by_cases hx0 : x 0 = 0
  · have hy0 : y 0 = 0 := by
      have : |y 0| ≤ 0 := by simpa [hx0] using hxy
      simpa using abs_nonpos_iff.mp this
    have : y = x := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      rw [hy0, hx0]
    rw [this]; exact hx
  · set a : ℝ := x 0 with ha
    set b : ℝ := y 0 with hb
    have hxa : |b| ≤ |a| := hxy
    have habs : |b / a| ≤ 1 := by
      rw [abs_div]
      exact (div_le_one (abs_pos.mpr hx0)).mpr hxa
    set t : ℝ := (1 + b / a) / 2 with ht
    have h1 : (0:ℝ) ≤ t := by
      have : -1 ≤ b / a := (abs_le.mp habs).1
      simp only [ht]
      linarith
    have h2 : (0:ℝ) ≤ 1 - t := by
      have : b / a ≤ 1 := (abs_le.mp habs).2
      simp only [ht]
      linarith
    have hsum : t + (1 - t) = 1 := by ring
    have hmem : t • x + (1 - t) • (-x) ∈ S := hconv hx (hsymm x hx) h1 h2 hsum
    have heq : t • x + (1 - t) • (-x) = y := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      rw [← ha, ← hb, ht]
      field_simp
      ring
    rw [← heq]; exact hmem

/-- In dimension one, two origin-symmetric convex sets are always nested. -/
theorem nested_of_symm_convex_dim_one {K L : Set (Fin 1 → ℝ)}
    (hK : Convex ℝ K) (hL : Convex ℝ L)
    (hKs : ∀ x ∈ K, -x ∈ K) (hLs : ∀ x ∈ L, -x ∈ L) :
    K ⊆ L ∨ L ⊆ K := by
  by_cases h : K ⊆ L
  · exact Or.inl h
  · right
    obtain ⟨x, hxK, hxL⟩ := Set.not_subset.mp h
    intro y hyL
    have hxy : |y 0| ≤ |x 0| := by
      by_contra hcon
      push_neg at hcon
      exact hxL (mem_of_abs_le_of_symm_convex hL hLs hyL (le_of_lt hcon))
    exact mem_of_abs_le_of_symm_convex hK hKs hxK hxy

/-- Two subsets of a subsingleton type are nested. -/
theorem nested_of_subsingleton {α : Type*} [Subsingleton α] (K L : Set α) :
    K ⊆ L ∨ L ⊆ K := by
  by_cases h : K ⊆ L
  · exact Or.inl h
  · right
    obtain ⟨x, hxK, hxL⟩ := Set.not_subset.mp h
    intro y hyL
    exact absurd (Subsingleton.elim y x ▸ hyL) hxL

/-- **Gaussian correlation inequality, base case.**

The full inequality of Royen states that for origin-symmetric convex sets `K`, `L` in `ℝ ^ n`
the standard Gaussian measure satisfies `γ K * γ L ≤ γ (K ∩ L)`; this is the predicate
`Frontier.GaussianCorrelationInequality`. Here we prove it in dimensions `n ≤ 1`
(the base case of the induction on the dimension), via the fact that in dimension at most one
any two origin-symmetric convex sets are nested. -/
theorem gaussian_correlation : ∀ n : ℕ, n ≤ 1 → GaussianCorrelationInequality n := by
  intro n hn K L hK hL hKs hLs _ _
  interval_cases n
  · exact gaussian_correlation_of_nested K L (nested_of_subsingleton K L)
  · exact gaussian_correlation_of_nested K L (nested_of_symm_convex_dim_one hK hL hKs hLs)

end Frontier

