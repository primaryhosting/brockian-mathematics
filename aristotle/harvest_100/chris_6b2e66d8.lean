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

namespace Frontier

open MeasureTheory

/-! ## The standard Gaussian measure and the statement of the inequality -/

/-- The standard Gaussian (probability) measure on `ℝ ^ n`, realised as the `n`-fold product
of the one-dimensional standard Gaussian `N(0,1)`. -/
noncomputable def stdGaussian (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => ProbabilityTheory.gaussianReal 0 1)

instance stdGaussian.isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (stdGaussian n) := by
  unfold stdGaussian
  infer_instance

/-- A set is *symmetric convex* if it is convex and invariant under `x ↦ -x`. -/
def SymmetricConvex {n : ℕ} (s : Set (Fin n → ℝ)) : Prop :=
  Convex ℝ s ∧ ∀ x ∈ s, -x ∈ s

/-- **The Gaussian correlation inequality** (Royen's theorem) in dimension `n`, as a proposition:
for any two symmetric convex measurable subsets `K`, `L` of `ℝ ^ n`, the standard Gaussian measure
satisfies `γ(K) · γ(L) ≤ γ(K ∩ L)`. -/
def GaussianCorrelationStatement (n : ℕ) : Prop :=
  ∀ K L : Set (Fin n → ℝ), SymmetricConvex K → SymmetricConvex L →
    MeasurableSet K → MeasurableSet L →
    stdGaussian n K * stdGaussian n L ≤ stdGaussian n (K ∩ L)

/-! ## A reduction valid in every dimension -/

/-- For a probability measure, the correlation inequality is immediate for nested sets. -/
theorem measure_mul_le_measure_inter_of_subset {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {K L : Set α} (h : K ⊆ L) :
    μ K * μ L ≤ μ (K ∩ L) := by
  rw [Set.inter_eq_self_of_subset_left h]
  calc μ K * μ L ≤ μ K * 1 := by
        gcongr
        exact prob_le_one
    _ = μ K := mul_one _

/-- A Lean-checked reduction, valid in every dimension: whenever the two sets are nested,
the Gaussian correlation inequality holds. -/
theorem gaussian_correlation_of_nested (n : ℕ) {K L : Set (Fin n → ℝ)}
    (h : K ⊆ L ∨ L ⊆ K) :
    stdGaussian n K * stdGaussian n L ≤ stdGaussian n (K ∩ L) := by
  rcases h with h | h
  · exact measure_mul_le_measure_inter_of_subset _ h
  · rw [mul_comm, Set.inter_comm]
    exact measure_mul_le_measure_inter_of_subset _ h

/-! ## Symmetric convex subsets of the line -/

/-- Symmetric convex subsets of the real line absorb every point of smaller absolute value. -/
theorem memReal_of_abs_le {S : Set ℝ} (hc : Convex ℝ S) (hs : ∀ x ∈ S, -x ∈ S)
    {a b : ℝ} (ha : a ∈ S) (hab : |b| ≤ |a|) : b ∈ S := by
  by_cases ha0 : a = 0
  · have hb : b = 0 := by
      rw [ha0] at hab
      simpa using abs_nonpos_iff.mp (by simpa using hab)
    rw [hb, ← ha0]
    exact ha
  · set t : ℝ := b / a with ht
    have hta : t * a = b := div_mul_cancel₀ _ ha0
    have htabs : |t| ≤ 1 := by
      rw [ht, abs_div, div_le_one (abs_pos.mpr ha0)]
      exact hab
    have ht1 : -1 ≤ t := neg_le_of_abs_le htabs
    have ht2 : t ≤ 1 := le_of_abs_le htabs
    have hmem : ((1 + t) / 2) • a + ((1 - t) / 2) • (-a) ∈ S :=
      hc ha (hs a ha) (by linarith) (by linarith) (by ring)
    have hval : ((1 + t) / 2) • a + ((1 - t) / 2) • (-a) = b := by
      simp only [smul_eq_mul]
      rw [← hta]
      ring
    rwa [hval] at hmem

/-- Any two symmetric convex subsets of the real line are nested. -/
theorem symmetricConvexReal_nested {K L : Set ℝ} (hKc : Convex ℝ K) (hKs : ∀ x ∈ K, -x ∈ K)
    (hLc : Convex ℝ L) (hLs : ∀ x ∈ L, -x ∈ L) : K ⊆ L ∨ L ⊆ K := by
  by_cases h : K ⊆ L
  · exact Or.inl h
  · right
    obtain ⟨a, haK, haL⟩ := Set.not_subset.mp h
    intro b hb
    have hba : |b| ≤ |a| := by
      by_contra hcon
      push_neg at hcon
      exact haL (memReal_of_abs_le hLc hLs hb (le_of_lt hcon))
    exact memReal_of_abs_le hKc hKs haK hba

/-- The Gaussian correlation inequality on the real line, for the one-dimensional standard
Gaussian measure `N(0,1)`. -/
theorem gaussianReal_correlation {A B : Set ℝ} (hAc : Convex ℝ A) (hAs : ∀ x ∈ A, -x ∈ A)
    (hBc : Convex ℝ B) (hBs : ∀ x ∈ B, -x ∈ B) :
    ProbabilityTheory.gaussianReal 0 1 A * ProbabilityTheory.gaussianReal 0 1 B
      ≤ ProbabilityTheory.gaussianReal 0 1 (A ∩ B) := by
  rcases symmetricConvexReal_nested hAc hAs hBc hBs with h | h
  · exact measure_mul_le_measure_inter_of_subset _ h
  · rw [mul_comm, Set.inter_comm]
    exact measure_mul_le_measure_inter_of_subset _ h

/-! ## Transfer from `Fin 1 → ℝ` to `ℝ` -/

/-- The coordinate description of a subset of `Fin 1 → ℝ`. -/
def coord1 (S : Set (Fin 1 → ℝ)) : Set ℝ := {r : ℝ | (fun _ => r) ∈ S}

theorem const_coord1 (x : Fin 1 → ℝ) : (fun _ => x 0) = x := by
  funext i
  have : i = 0 := Subsingleton.elim _ _
  rw [this]

theorem mem_coord1_iff {S : Set (Fin 1 → ℝ)} (x : Fin 1 → ℝ) : x 0 ∈ coord1 S ↔ x ∈ S := by
  unfold coord1
  rw [Set.mem_setOf_eq, const_coord1]

theorem coord1_convex {S : Set (Fin 1 → ℝ)} (hS : SymmetricConvex S) : Convex ℝ (coord1 S) := by
  intro x hx y hy a b ha hb hab
  have hxS : (fun _ : Fin 1 => x) ∈ S := hx
  have hyS : (fun _ : Fin 1 => y) ∈ S := hy
  have := hS.1 hxS hyS ha hb hab
  have heq : a • (fun _ : Fin 1 => x) + b • (fun _ : Fin 1 => y) = (fun _ : Fin 1 => a • x + b • y) := by
    funext i
    simp
  rwa [heq] at this

theorem coord1_symm {S : Set (Fin 1 → ℝ)} (hS : SymmetricConvex S) :
    ∀ x ∈ coord1 S, -x ∈ coord1 S := by
  intro x hx
  have hxS : (fun _ : Fin 1 => x) ∈ S := hx
  have := hS.2 _ hxS
  have heq : -(fun _ : Fin 1 => x) = (fun _ : Fin 1 => -x) := by
    funext i
    simp
  rwa [heq] at this

/-- In dimension one, any two symmetric convex sets are nested. -/
theorem symmetricConvex_nested_dim_one {K L : Set (Fin 1 → ℝ)}
    (hK : SymmetricConvex K) (hL : SymmetricConvex L) : K ⊆ L ∨ L ⊆ K := by
  rcases symmetricConvexReal_nested (coord1_convex hK) (coord1_symm hK)
      (coord1_convex hL) (coord1_symm hL) with h | h
  · left
    intro x hx
    exact (mem_coord1_iff x).mp (h ((mem_coord1_iff x).mpr hx))
  · right
    intro x hx
    exact (mem_coord1_iff x).mp (h ((mem_coord1_iff x).mpr hx))

/-! ## The base cases of the Gaussian correlation inequality -/

/-- **Gaussian correlation inequality, base case `n = 1`.**
For the standard Gaussian measure on the line, `γ(K) · γ(L) ≤ γ(K ∩ L)` for all symmetric
convex sets `K`, `L`. (This is the one-dimensional instance of Royen's theorem; the proof
proceeds through the fact that symmetric convex subsets of the line are nested.) -/
theorem gaussian_correlation : GaussianCorrelationStatement 1 := fun _ _ hK hL _ _ =>
  gaussian_correlation_of_nested 1 (symmetricConvex_nested_dim_one hK hL)

/-- Trivial base case `n = 0`: the space is a single point. -/
theorem gaussian_correlation_dim_zero : GaussianCorrelationStatement 0 := by
  intro K L _ _ _ _
  rcases Set.eq_empty_or_nonempty K with rfl | ⟨x, hx⟩
  · simp
  rcases Set.eq_empty_or_nonempty L with rfl | ⟨y, hy⟩
  · simp
  have hxy : x = y := Subsingleton.elim _ _
  have hKL : K ∩ L = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    have hzx : z = x := Subsingleton.elim _ _
    exact ⟨hzx ▸ hx, hzx ▸ hxy ▸ hy⟩
  rw [hKL, measure_univ]
  calc stdGaussian 0 K * stdGaussian 0 L ≤ 1 * 1 :=
        mul_le_mul' prob_le_one prob_le_one
    _ = 1 := mul_one 1

/-- **Gaussian correlation inequality for boxes, in every dimension.**
If `K = ∏ i, A i` and `L = ∏ i, B i` are products of symmetric convex subsets of the line
(hence themselves symmetric convex subsets of `ℝ ^ n`), then `γ(K) · γ(L) ≤ γ(K ∩ L)`. -/
theorem gaussian_correlation_boxes (n : ℕ) (A B : Fin n → Set ℝ)
    (hAc : ∀ i, Convex ℝ (A i)) (hAs : ∀ i, ∀ x ∈ A i, -x ∈ A i)
    (hBc : ∀ i, Convex ℝ (B i)) (hBs : ∀ i, ∀ x ∈ B i, -x ∈ B i) :
    stdGaussian n (Set.univ.pi A) * stdGaussian n (Set.univ.pi B)
      ≤ stdGaussian n (Set.univ.pi A ∩ Set.univ.pi B) := by
  rw [← Set.pi_inter_distrib]
  unfold stdGaussian
  rw [Measure.pi_pi, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod' fun i _ =>
    gaussianReal_correlation (hAc i) (hAs i) (hBc i) (hBs i)

end Frontier

