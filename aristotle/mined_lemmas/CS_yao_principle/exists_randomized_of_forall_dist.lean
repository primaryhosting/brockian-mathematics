/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to come before any module docstring, so the required header appears
-- at the top of the file as a plain comment and again here as the module docstring.)

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

set_option grind.warning false

namespace CS

variable {A I : Type*} [Fintype A] [Fintype I] [Nonempty A] [Nonempty I]

/-- The worst-case expected cost of the randomized algorithm given by the distribution `p`
over deterministic algorithms:  `max over inputs i of  E_{a ~ p} [c a i]`. -/

theorem exists_randomized_of_forall_dist (c : A → I → ℝ) (v : ℝ)
    (hv : ∀ q ∈ stdSimplex ℝ I, ∃ a, ∑ i, q i * c a i ≤ v) :
    ∃ p ∈ stdSimplex ℝ A, ∀ i, ∑ a, p a * c a i ≤ v := by
  classical
  by_contra hcon
  push_neg at hcon
  -- the set of achievable expected-cost vectors
  set K : Set (I → ℝ) := (expMap c) '' (stdSimplex ℝ A) with hK
  have hKconv : Convex ℝ K := (convex_stdSimplex ℝ A).linear_image (expMap c)
  have hKcomp : IsCompact K := (isCompact_stdSimplex A).image (continuous_expMap c)
  -- the "good" region
  set T : Set (I → ℝ) := {y | ∀ i, y i ≤ v} with hT
  have hTconv : Convex ℝ T := by
    intro y hy y' hy' s t hs ht hst i
    have h1 : y i ≤ v := hy i
    have h2 : y' i ≤ v := hy' i
    have hsm : (s • y + t • y') i = s * y i + t * y' i := rfl
    rw [hsm]
    have k1 : s * y i ≤ s * v := mul_le_mul_of_nonneg_left h1 hs
    have k2 : t * y' i ≤ t * v := mul_le_mul_of_nonneg_left h2 ht
    have : s * v + t * v = v := by rw [← add_mul, hst, one_mul]
    linarith
  have hTclosed : IsClosed T := by
    have : T = ⋂ i : I, {y : I → ℝ | y i ≤ v} := by
      ext y; simp [hT, Set.mem_iInter]
    rw [this]
    exact isClosed_iInter fun i => isClosed_le (continuous_apply i) continuous_const
  have hdisj : Disjoint K T := by
    rw [Set.disjoint_left]
    rintro y ⟨p, hp, rfl⟩ hyT
    obtain ⟨i, hi⟩ := hcon p hp
    exact absurd (hyT i) (not_le.mpr hi)
  obtain ⟨f, u, w, hfK, huw, hfT⟩ :=
    geometric_hahn_banach_compact_closed hKconv hKcomp hTconv hTclosed hdisj
  -- the coefficients of `-f`
  set q : I → ℝ := fun i => -f (Pi.single i 1) with hq
  have hfy : ∀ y : I → ℝ, f y = -∑ i, y i * q i := by
    intro y
    rw [clm_apply_eq_sum f y, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hq]
  -- the constant vector `v`
  have hcv : (fun _ : I => v) ∈ T := fun _ => le_refl v
  have hfcv : w < f (fun _ : I => v) := hfT _ hcv
  -- the coefficients are nonnegative
  have hqnonneg : ∀ i, 0 ≤ q i := by
    intro i
    by_contra hneg
    push_neg at hneg
    set lam : ℝ := (f (fun _ : I => v) - w + 1) / (-q i) with hlam
    have hqpos : 0 < -q i := by linarith
    have hlamnonneg : 0 ≤ lam := by
      apply div_nonneg _ (le_of_lt hqpos); linarith
    set y : I → ℝ := (fun _ : I => v) - lam • (Pi.single i 1 : I → ℝ) with hy
    have hyT : y ∈ T := by
      intro j
      by_cases h : j = i
      · subst h
        have : y j = v - lam := by simp [hy]
        rw [this]; linarith
      · have : y j = v := by simp [hy, h]
        rw [this]
    have h1 : f y = f (fun _ : I => v) - lam * f (Pi.single i 1) := by
      rw [hy, map_sub, map_smul, smul_eq_mul]
    have h2 : f (Pi.single i (1 : ℝ)) = -q i := by simp [hq]
    have h3 : lam * (-q i) = f (fun _ : I => v) - w + 1 := by
      rw [hlam, div_mul_cancel₀ _ (ne_of_gt hqpos)]
    have := hfT y hyT
    rw [h1, h2] at this
    nlinarith
  -- for every distribution over algorithms, the separating functional gives a strict inequality
  have hmain : ∀ p ∈ stdSimplex ℝ A, v * (∑ i, q i) < ∑ i, (∑ a, p a * c a i) * q i := by
    intro p hp
    have h1 : f ((expMap c) p) < u := hfK _ ⟨p, hp, rfl⟩
    have h2 : (expMap c) p = fun i => ∑ a, p a * c a i := rfl
    rw [h2, hfy] at h1
    have h3 : w < -∑ i, v * q i := by
      have := hfcv
      rw [hfy] at this
      exact this
    have h4 : ∑ i, v * q i = v * ∑ i, q i := by rw [Finset.mul_sum]
    rw [h4] at h3
    linarith
  -- total mass is positive
  have hQpos : 0 < ∑ i, q i := by
    rcases lt_or_eq_of_le (Finset.sum_nonneg fun i _ => hqnonneg i) with h | h
    · exact h
    · exfalso
      have hall : ∀ i ∈ Finset.univ, q i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hqnonneg i).mp h.symm
      obtain ⟨p, hp⟩ := (stdSimplex_nonempty : (stdSimplex ℝ A).Nonempty)
      have := hmain p hp
      rw [Finset.sum_congr rfl (fun i hi => by rw [hall i hi]; ring : ∀ i ∈ Finset.univ,
        (∑ a, p a * c a i) * q i = 0)] at this
      rw [← h] at this
      simp at this
  -- normalize to an input distribution
  set Q : ℝ := ∑ i, q i with hQ
  set qhat : I → ℝ := fun i => q i / Q with hqhat
  have hqhatmem : qhat ∈ stdSimplex ℝ I := by
    refine ⟨fun i => div_nonneg (hqnonneg i) (le_of_lt hQpos), ?_⟩
    rw [hqhat, ← Finset.sum_div, ← hQ, div_self (ne_of_gt hQpos)]
  obtain ⟨a, ha⟩ := hv qhat hqhatmem
  -- but the point mass at `a` contradicts the strict inequality
  have hpa : (Pi.single a 1 : A → ℝ) ∈ stdSimplex ℝ A := single_mem_stdSimplex a
  have h5 := hmain _ hpa
  have h6 : ∀ i, ∑ a', (Pi.single a (1 : ℝ) : A → ℝ) a' * c a' i = c a i := by
    intro i; simp [Pi.single_apply, Finset.sum_ite_eq']
  rw [Finset.sum_congr rfl (fun i _ => by rw [h6 i] : ∀ i ∈ Finset.univ,
    (∑ a', (Pi.single a (1 : ℝ) : A → ℝ) a' * c a' i) * q i = c a i * q i)] at h5
  have h7 : ∑ i, qhat i * c a i = (∑ i, c a i * q i) / Q := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hqhat]; ring
  rw [h7] at ha
  rw [div_le_iff₀ hQpos] at ha
  linarith

/-! ### Yao's minimax principle -/

/-- **Yao's principle.**  For a finite cost matrix `c` indexed by deterministic algorithms `A`
and inputs `I`, the optimal worst-case expected cost of a randomized algorithm equals the
optimal distributional complexity:

`min_{p ∈ Δ(A)} max_{i ∈ I} E_{a ~ p}[c a i]  =  max_{q ∈ Δ(I)} min_{a ∈ A} E_{i ~ q}[c a i]`. -/
