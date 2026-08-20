import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
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

namespace CS

open Set

variable {A I : Type*} [Fintype A] [Fintype I]

/-- The expected cost of the randomized algorithm given by the distribution `p` over the
deterministic algorithms `A`, run on the input `i`. -/

lemma exists_input_dist_of_forall_alg [Nonempty A] [Nonempty I] (c : A → I → ℝ) (v : ℝ)
    (h : ∀ p ∈ stdSimplex ℝ A, ∃ i, v < expCostAlg c p i) :
    ∃ q ∈ stdSimplex ℝ I, ∀ a, v < expCostInp c q a := by
  classical
  set g : (A → ℝ) → (I → ℝ) := fun p i => expCostAlg c p i with hgdef
  set K : Set (I → ℝ) := g '' stdSimplex ℝ A with hKdef
  set Q : Set (I → ℝ) := {y : I → ℝ | ∀ i, 0 ≤ y i} with hQdef
  set C : Set (I → ℝ) := K + Q with hCdef
  -- `C` is the set of cost vectors dominating some randomized algorithm's cost vector
  have hmemC : ∀ y : I → ℝ, y ∈ C ↔ ∃ p ∈ stdSimplex ℝ A, ∀ i, expCostAlg c p i ≤ y i := by
    intro y
    rw [hCdef, Set.mem_add]
    constructor
    · rintro ⟨k, ⟨p, hp, rfl⟩, z, hz, rfl⟩
      refine ⟨p, hp, fun i => ?_⟩
      have hzi : (0 : ℝ) ≤ z i := hz i
      show expCostAlg c p i ≤ g p i + z i
      have : g p i = expCostAlg c p i := rfl
      linarith
    · rintro ⟨p, hp, hle⟩
      refine ⟨g p, ⟨p, hp, rfl⟩, y - g p, fun i => ?_, by funext i; simp⟩
      have := hle i
      simpa [hgdef] using sub_nonneg.2 this
  -- closedness
  have hgcont : Continuous g := by
    apply continuous_pi
    intro i
    exact continuous_finset_sum _ fun a _ => (continuous_apply a).mul continuous_const
  have hKcompact : IsCompact K := (isCompact_stdSimplex A).image hgcont
  have hQclosed : IsClosed Q := by
    have hQeq : Q = ⋂ i : I, (fun y : I → ℝ => y i) ⁻¹' (Set.Ici (0 : ℝ)) := by
      ext y; simp [hQdef]
    rw [hQeq]
    exact isClosed_iInter fun i => isClosed_Ici.preimage (continuous_apply i)
  have hCclosed : IsClosed C := hQclosed.add_left_of_isCompact hKcompact
  -- convexity
  have hCconv : Convex ℝ C := by
    intro y₁ hy₁ y₂ hy₂ s t hs ht hst
    rw [hmemC] at hy₁ hy₂
    rw [hmemC]
    obtain ⟨p₁, hp₁, k₁⟩ := hy₁
    obtain ⟨p₂, hp₂, k₂⟩ := hy₂
    refine ⟨s • p₁ + t • p₂, convex_stdSimplex ℝ A hp₁ hp₂ hs ht hst, fun i => ?_⟩
    have hlin : expCostAlg c (s • p₁ + t • p₂) i
        = s * expCostAlg c p₁ i + t * expCostAlg c p₂ i := by
      simp only [expCostAlg, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by simp [Pi.add_apply, Pi.smul_apply]; ring
    have h1 := mul_le_mul_of_nonneg_left (k₁ i) hs
    have h2 := mul_le_mul_of_nonneg_left (k₂ i) ht
    have : (s • y₁ + t • y₂) i = s * y₁ i + t * y₂ i := by simp
    rw [hlin, this]
    linarith
  -- the constant vector `v` is not in `C`
  have hx₀ : (fun _ : I => v) ∉ C := by
    rw [hmemC]
    rintro ⟨p, hp, hle⟩
    obtain ⟨i, hi⟩ := h p hp
    exact absurd (hle i) (not_le.2 hi)
  -- upward closure of `C`
  have hup : ∀ y ∈ C, ∀ z : I → ℝ, (∀ i, y i ≤ z i) → z ∈ C := by
    intro y hy z hz
    rw [hmemC] at hy ⊢
    obtain ⟨p, hp, hle⟩ := hy
    exact ⟨p, hp, fun i => (hle i).trans (hz i)⟩
  have hcC : ∀ a : A, (fun i => c a i) ∈ C := by
    intro a
    rw [hmemC]
    exact ⟨Pi.single a 1, single_mem_stdSimplex ℝ a, fun i => by rw [expCostAlg_single]⟩
  -- separate
  obtain ⟨f, u, hfx, hfC⟩ := geometric_hahn_banach_point_closed hCconv hCclosed hx₀
  set lam : I → ℝ := fun i => f (Pi.single i (1 : ℝ) : I → ℝ) with hlamdef
  have hf_apply : ∀ y : I → ℝ, f y = ∑ i, y i * lam i := by
    intro y
    have hy : y = ∑ i, y i • (Pi.single i (1 : ℝ) : I → ℝ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
    conv_lhs => rw [hy]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; simp [hlamdef, smul_eq_mul]
  -- the separating functional has nonnegative coefficients
  have hlamnn : ∀ i, 0 ≤ lam i := by
    intro i
    by_contra hneg
    push_neg at hneg
    set a₀ := Classical.arbitrary A with ha₀
    set y : I → ℝ := fun j => c a₀ j with hy
    have hyC : y ∈ C := hcC a₀
    have hfy : u < f y := hfC y hyC
    set s : ℝ := (f y - u) / (-lam i) with hs
    have hs0 : 0 ≤ s := div_nonneg (by linarith) (by linarith)
    have hzC : (y + s • (Pi.single i (1 : ℝ) : I → ℝ)) ∈ C := by
      refine hup y hyC _ fun j => ?_
      have hnn : (0 : ℝ) ≤ s * (Pi.single i (1 : ℝ) : I → ℝ) j := by
        refine mul_nonneg hs0 ?_
        rcases eq_or_ne i j with rfl | hij
        · simp
        · simp [hij]
      simpa using hnn
    have hgt := hfC _ hzC
    rw [map_add, map_smul] at hgt
    have hne : lam i ≠ 0 := ne_of_lt hneg
    have hsl : s * lam i = -(f y - u) := by
      rw [hs]
      field_simp
    simp only [smul_eq_mul] at hgt
    linarith
  set S : ℝ := ∑ i, lam i with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hlamnn i
  have hSpos : 0 < S := by
    rcases lt_or_eq_of_le hS0 with hlt | heq
    · exact hlt
    · exfalso
      have hall : ∀ i ∈ (Finset.univ : Finset I), lam i = 0 := by
        refine (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hlamnn i).1 ?_
        rw [← hSdef, ← heq]
      have hf0 : ∀ y : I → ℝ, f y = 0 := by
        intro y
        rw [hf_apply y]
        exact Finset.sum_eq_zero fun i _ => by rw [hall i (Finset.mem_univ i), mul_zero]
      have h1 : (0 : ℝ) < u := by
        have := hfx
        rw [hf0] at this
        exact this
      have h2 : u < 0 := by
        have := hfC _ (hcC (Classical.arbitrary A))
        rw [hf0] at this
        exact this
      linarith
  refine ⟨fun i => lam i / S, ⟨fun i => div_nonneg (hlamnn i) hSpos.le, ?_⟩, fun a => ?_⟩
  · rw [← Finset.sum_div, ← hSdef]
    field_simp
  · have h1 : u < ∑ i, c a i * lam i := by
      have := hfC _ (hcC a)
      rwa [hf_apply] at this
    have h2 : v * S < u := by
      have := hfx
      rw [hf_apply] at this
      simpa [hSdef, Finset.mul_sum] using this
    have h3 : v * S < ∑ i, c a i * lam i := lt_trans h2 h1
    have h4 : expCostInp c (fun i => lam i / S) a = (∑ i, c a i * lam i) / S := by
      rw [expCostInp, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h4, lt_div_iff₀ hSpos]
    exact h3

/-- **Yao's minimax principle.** For a finite cost matrix `c : A → I → ℝ`, the randomized
complexity (the minimum over distributions on deterministic algorithms of the worst-case
expected cost) equals the distributional complexity (the maximum over input distributions of
the best deterministic algorithm's expected cost). -/
