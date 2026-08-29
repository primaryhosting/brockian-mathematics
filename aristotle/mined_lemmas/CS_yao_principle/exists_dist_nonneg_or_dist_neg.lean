/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is repeated as a module docstring below; Lean requires `import`
-- to precede any module docstring.)

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

variable {A I : Type*}

/-- The expected cost of the randomized algorithm given by the distribution `p` over the
(deterministic) algorithms `A`, run on the input `i`. -/

theorem exists_dist_nonneg_or_dist_neg [Nonempty A] [Nonempty I] (M : A → I → ℝ) :
    (∃ q ∈ stdSimplex ℝ I, ∀ a, 0 ≤ ∑ i, q i * M a i) ∨
    (∃ p ∈ stdSimplex ℝ A, ∀ i, ∑ a, p a * M a i < 0) := by
  classical
  by_cases hcase : ∃ q ∈ stdSimplex ℝ I, ∀ a, 0 ≤ ∑ i, q i * M a i
  · exact Or.inl hcase
  refine Or.inr ?_
  push_neg at hcase
  -- The linear map sending an input distribution `q` to the vector of expected costs.
  set L : (I → ℝ) →ₗ[ℝ] (A → ℝ) :=
    { toFun := fun q a => ∑ i, q i * M a i
      map_add' := by intro x y; funext a; simp [← Finset.sum_add_distrib, add_mul]
      map_smul' := by intro c x; funext a; simp [Finset.mul_sum, mul_assoc] } with hL
  have hLdef : ∀ (q : I → ℝ) (a : A), L q a = ∑ i, q i * M a i := fun q a => rfl
  set K : Set (A → ℝ) := L '' (stdSimplex ℝ I) with hK
  set P : Set (A → ℝ) := {y : A → ℝ | ∀ a, 0 ≤ y a} with hP
  have hKconv : Convex ℝ K := (convex_stdSimplex ℝ I).linear_image L
  have hKcomp : IsCompact K := (isCompact_stdSimplex I).image L.continuous_of_finiteDimensional
  have hPconv : Convex ℝ P := by
    intro x hx y hy s t hs ht _ a
    have h1 := hx a
    have h2 := hy a
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h3 := mul_nonneg hs h1
    have h4 := mul_nonneg ht h2
    linarith
  have hPclosed : IsClosed P := by
    have hPeq : P = ⋂ a, {y : A → ℝ | 0 ≤ y a} := by ext y; simp [hP]
    rw [hPeq]
    exact isClosed_iInter fun a => isClosed_le continuous_const (continuous_apply a)
  have hdisj : Disjoint K P := by
    rw [Set.disjoint_left]
    rintro _ ⟨q, hq, rfl⟩ hmem
    obtain ⟨a, ha⟩ := hcase q hq
    have h := hmem a
    rw [hLdef] at h
    linarith
  obtain ⟨f, u, v, hfK, huv, hfP⟩ :=
    geometric_hahn_banach_compact_closed hKconv hKcomp hPconv hPclosed hdisj
  -- The separating functional has nonnegative coefficients, giving the desired distribution.
  set p : A → ℝ := fun a => f (Pi.single a 1) with hp
  have hv0 : v < 0 := by
    have := hfP 0 (fun a => le_refl 0)
    simpa using this
  have hpnonneg : ∀ a, 0 ≤ p a := by
    intro a
    by_contra hlt
    push_neg at hlt
    have hne : p a ≠ 0 := ne_of_lt hlt
    set t : ℝ := v / p a + 1 with ht
    have ht0 : 0 ≤ t := by
      have : 0 < v / p a := div_pos_of_neg_of_neg hv0 hlt
      linarith
    have hmem : (t • (Pi.single a (1:ℝ) : A → ℝ)) ∈ P := by
      intro b
      rcases eq_or_ne b a with rfl | hb
      · simpa using ht0
      · simp [hb]
    have h1 := hfP _ hmem
    rw [map_smul] at h1
    have h2 : t * p a = v + p a := by
      rw [ht, add_mul, one_mul, div_mul_cancel₀ _ hne]
    simp only [smul_eq_mul] at h1
    rw [h2] at h1
    linarith
  have hfx : ∀ x : A → ℝ, f x = ∑ a, x a * p a := by
    intro x
    have hx : x = ∑ a, x a • (Pi.single a (1:ℝ) : A → ℝ) := by
      funext b
      simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
    conv_lhs => rw [hx]
    rw [map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul]; simp [hp]
  have key : ∀ i, ∑ a, p a * M a i < 0 := by
    intro i
    have hδ : (Pi.single i (1:ℝ) : I → ℝ) ∈ stdSimplex ℝ I := by
      refine ⟨fun j => ?_, ?_⟩
      · rcases eq_or_ne j i with rfl | hj
        · simp
        · simp [hj]
      · simp
    have h1 := hfK _ ⟨_, hδ, rfl⟩
    have h2 : f (L (Pi.single i (1:ℝ) : I → ℝ)) = ∑ a, p a * M a i := by
      rw [hfx]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hLdef]
      simp [Pi.single_apply, mul_comm]
    rw [h2] at h1
    linarith
  have hSnonneg : 0 ≤ ∑ a, p a := Finset.sum_nonneg fun a _ => hpnonneg a
  have hS : 0 < ∑ a, p a := by
    rcases hSnonneg.lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨i⟩ := ‹Nonempty I›
      have hall : ∀ a ∈ Finset.univ, p a = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun a _ => hpnonneg a).1 h.symm
      have hk := key i
      rw [Finset.sum_congr rfl fun a ha => by rw [hall a ha, zero_mul]] at hk
      simp at hk
  refine ⟨fun a => p a / (∑ a, p a), ⟨fun a => div_nonneg (hpnonneg a) hS.le, ?_⟩, ?_⟩
  · rw [← Finset.sum_div, div_self (ne_of_gt hS)]
  · intro i
    have h3 : ∑ a, p a / (∑ a, p a) * M a i = (∑ a, p a * M a i) / (∑ a, p a) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [h3]
    exact div_neg_of_neg_of_pos (key i) hS

end Alternative

section Main

variable [Fintype A] [Fintype I] [Nonempty A] [Nonempty I]

/-- Uniform bounds on all the entries of the cost matrix. -/
