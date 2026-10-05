import Mathlib
/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace CS

variable {A X : Type*} [Fintype A] [Fintype X]

/-- Expected cost of the mixed (randomized) algorithm strategy `q` on the input `x`. -/
def mixedCost (cost : A → X → ℝ) (q : A → ℝ) (x : X) : ℝ := ∑ a, q a * cost a x

/-- Expected cost of the deterministic algorithm `a` on an input drawn from the
distribution `p`. -/
def avgCost (cost : A → X → ℝ) (p : X → ℝ) (a : A) : ℝ := ∑ x, p x * cost a x

/-- The randomized complexity: the least, over randomized algorithms (distributions `q`
over deterministic algorithms), of the worst-case expected cost. -/
noncomputable def randomizedComplexity (cost : A → X → ℝ) : ℝ :=
  sInf ((fun q => ⨆ x, mixedCost cost q x) '' stdSimplex ℝ A)

/-- The distributional complexity: the greatest, over input distributions `p`, of the
best expected cost of a deterministic algorithm. -/
noncomputable def distributionalComplexity (cost : A → X → ℝ) : ℝ :=
  sSup ((fun p => ⨅ a, avgCost cost p a) '' stdSimplex ℝ X)

/-- The linear map sending a mixed strategy over algorithms to its cost vector. -/
noncomputable def mixedMap (cost : A → X → ℝ) : (A → ℝ) →ₗ[ℝ] (X → ℝ) where
  toFun q := mixedCost cost q
  map_add' q r := by
    funext x; simp [mixedCost, add_mul, Finset.sum_add_distrib]
  map_smul' c q := by
    funext x; simp [mixedCost, Finset.mul_sum, mul_assoc]

/-- A point mass is a probability distribution. -/
lemma single_mem_stdSimplex (ι : Type*) [Fintype ι] [DecidableEq ι] (i : ι) :
    (Pi.single i (1 : ℝ)) ∈ stdSimplex ℝ ι := by
  refine ⟨fun j => ?_, by simp⟩
  rcases eq_or_ne i j with rfl | h <;> simp [*]

/-- Weak duality: any input distribution gives a lower bound on any randomized
algorithm's worst case cost. -/
lemma inf_avgCost_le_sup_mixedCost [Nonempty A] [Nonempty X] (cost : A → X → ℝ)
    {p : X → ℝ} (hp : p ∈ stdSimplex ℝ X) {q : A → ℝ} (hq : q ∈ stdSimplex ℝ A) :
    (⨅ a, avgCost cost p a) ≤ ⨆ x, mixedCost cost q x := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hq0, hq1⟩ := hq
  set m := ⨅ a, avgCost cost p a with hm
  set M := ⨆ x, mixedCost cost q x with hM
  have hmle : ∀ a, m ≤ avgCost cost p a := fun a => ciInf_le (Finite.bddBelow_range _) a
  have hMle : ∀ x, mixedCost cost q x ≤ M := fun x => le_ciSup (Finite.bddAbove_range _) x
  have h1 : m = ∑ a, q a * m := by rw [← Finset.sum_mul, hq1, one_mul]
  have h2 : ∑ a, q a * m ≤ ∑ a, q a * avgCost cost p a :=
    Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hmle a) (hq0 a)
  have h3 : ∑ a, q a * avgCost cost p a = ∑ x, p x * mixedCost cost q x := by
    simp only [avgCost, mixedCost, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a _ => by ring
  have h4 : ∑ x, p x * mixedCost cost q x ≤ ∑ x, p x * M :=
    Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hMle x) (hp0 x)
  have h5 : ∑ x, p x * M = M := by rw [← Finset.sum_mul, hp1, one_mul]
  linarith [h1, h2, h3, h4, h5]

omit [Fintype X] in
lemma randomizedSet_nonempty [Nonempty A] [DecidableEq A] (cost : A → X → ℝ) :
    ((fun q => ⨆ x, mixedCost cost q x) '' stdSimplex ℝ A).Nonempty :=
  ⟨_, Set.mem_image_of_mem _ (single_mem_stdSimplex A (Classical.arbitrary A))⟩

omit [Fintype A] in
lemma distributionalSet_nonempty [Nonempty X] [DecidableEq X] (cost : A → X → ℝ) :
    ((fun p => ⨅ a, avgCost cost p a) '' stdSimplex ℝ X).Nonempty :=
  ⟨_, Set.mem_image_of_mem _ (single_mem_stdSimplex X (Classical.arbitrary X))⟩

lemma randomizedSet_bddBelow [Nonempty A] [Nonempty X] [DecidableEq X] (cost : A → X → ℝ) :
    BddBelow ((fun q => ⨆ x, mixedCost cost q x) '' stdSimplex ℝ A) := by
  refine ⟨⨅ a, avgCost cost (Pi.single (Classical.arbitrary X) 1) a, ?_⟩
  rintro y ⟨q, hq, rfl⟩
  exact inf_avgCost_le_sup_mixedCost cost (single_mem_stdSimplex X _) hq

lemma distributionalSet_bddAbove [Nonempty A] [Nonempty X] [DecidableEq A] (cost : A → X → ℝ) :
    BddAbove ((fun p => ⨅ a, avgCost cost p a) '' stdSimplex ℝ X) := by
  refine ⟨⨆ x, mixedCost cost (Pi.single (Classical.arbitrary A) 1) x, ?_⟩
  rintro y ⟨p, hp, rfl⟩
  exact inf_avgCost_le_sup_mixedCost cost hp (single_mem_stdSimplex A _)

lemma distributional_le_randomized [Nonempty A] [Nonempty X] [DecidableEq A] [DecidableEq X]
    (cost : A → X → ℝ) :
    distributionalComplexity cost ≤ randomizedComplexity cost := by
  apply csSup_le (distributionalSet_nonempty cost)
  rintro y ⟨p, hp, rfl⟩
  apply le_csInf (randomizedSet_nonempty cost)
  rintro z ⟨q, hq, rfl⟩
  exact inf_avgCost_le_sup_mixedCost cost hp hq

/-- The hard direction, via separation of the compact convex set of achievable cost vectors
from the closed convex set of vectors bounded by `c`: for every `c` strictly below the
randomized complexity there is an input distribution witnessing that the distributional
complexity is at least `c`. -/
lemma exists_hard_distribution [Nonempty A] [Nonempty X] [DecidableEq A] [DecidableEq X]
    (cost : A → X → ℝ) {c : ℝ} (hc : c < randomizedComplexity cost) :
    ∃ p ∈ stdSimplex ℝ X, ∀ a, c ≤ avgCost cost p a := by
  classical
  set K := (mixedMap cost) '' (stdSimplex ℝ A) with hK
  have hKc : IsCompact K :=
    (isCompact_stdSimplex A).image (LinearMap.continuous_of_finiteDimensional _)
  have hKconv : Convex ℝ K := (convex_stdSimplex ℝ A).linear_image _
  set L : Set (X → ℝ) := {y : X → ℝ | ∀ x, y x ≤ c} with hL
  have hLconv : Convex ℝ L := by
    intro y hy z hz s t hs ht hst x
    have h1 := hy x
    have h2 := hz x
    have he : (s • y + t • z) x = s * y x + t * z x := rfl
    have hc' : s * c + t * c = c := by rw [← add_mul, hst, one_mul]
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left h1 hs, mul_le_mul_of_nonneg_left h2 ht]
  have hLclosed : IsClosed L := by
    have hLeq : L = ⋂ x : X, {y : X → ℝ | y x ≤ c} := by ext y; simp [hL]
    rw [hLeq]
    exact isClosed_iInter fun x => isClosed_le (continuous_apply x) continuous_const
  have hdisj : Disjoint L K := by
    rw [Set.disjoint_left]
    rintro y hy ⟨q, hq, rfl⟩
    have h1 : randomizedComplexity cost ≤ ⨆ x, mixedCost cost q x :=
      csInf_le (randomizedSet_bddBelow cost) ⟨q, hq, rfl⟩
    have h2 : (⨆ x, mixedCost cost q x) ≤ c := ciSup_le fun x => hy x
    linarith
  obtain ⟨f, u, v, hfL, huv, hfK⟩ :=
    geometric_hahn_banach_closed_compact hLconv hLclosed hKconv hKc hdisj
  set p : X → ℝ := fun x => f (Pi.single x 1) with hp
  have hfrep : ∀ y : X → ℝ, f y = ∑ x, y x * p x := by
    intro y
    conv_lhs => rw [← Finset.univ_sum_single y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hsm : Pi.single x (y x) = (y x) • (Pi.single x (1 : ℝ) : X → ℝ) := by
      funext z; by_cases h : z = x <;> simp [Pi.single_apply, h]
    rw [hsm, map_smul]
    simp [hp]
  have hconst : f (fun _ => c) = c * ∑ x, p x := by rw [hfrep, Finset.mul_sum]
  have hconstL : (fun _ => c) ∈ L := fun _ => le_rfl
  have hCu : c * ∑ x, p x < u := by rw [← hconst]; exact hfL _ hconstL
  have hpnonneg : ∀ x0, 0 ≤ p x0 := by
    intro x0
    by_contra hneg
    push_neg at hneg
    set C := c * ∑ x, p x with hC
    set t := (u - C + 1) / (-p x0) with ht
    have hpos : 0 < -p x0 := by linarith
    have ht0 : 0 ≤ t := by
      apply div_nonneg _ (le_of_lt hpos); linarith
    set y : X → ℝ := (fun _ => c) - t • (Pi.single x0 (1 : ℝ) : X → ℝ) with hy
    have hyL : y ∈ L := by
      intro x
      have hyx : y x = c - t * (Pi.single x0 (1 : ℝ) : X → ℝ) x := rfl
      have hnn : 0 ≤ t * (Pi.single x0 (1 : ℝ) : X → ℝ) x := by
        refine mul_nonneg ht0 ?_
        by_cases h : x = x0 <;> simp [Pi.single_apply, h]
      rw [hyx]; linarith
    have hfy : f y = C - t * p x0 := by
      rw [hy, map_sub, map_smul, hconst]
      simp [hp, hC]
    have hlt := hfL y hyL
    rw [hfy] at hlt
    have hval : t * (-p x0) = u - C + 1 := by
      rw [ht]; exact div_mul_cancel₀ _ (ne_of_gt hpos)
    nlinarith
  have hSpos : 0 < ∑ x, p x := by
    rcases lt_or_eq_of_le (Finset.sum_nonneg fun x _ => hpnonneg x) with h | h
    · exact h
    · exfalso
      have hzero : ∀ x, p x = 0 := fun x =>
        (Finset.sum_eq_zero_iff_of_nonneg fun x _ => hpnonneg x).mp h.symm x (Finset.mem_univ x)
      have hf0 : ∀ y : X → ℝ, f y = 0 := by
        intro y; rw [hfrep]; simp [hzero]
      have h1 : (0 : ℝ) < u := by
        have hlt := hfL _ hconstL
        rw [hf0] at hlt; exact hlt
      obtain ⟨k, hk⟩ : K.Nonempty :=
        ⟨_, Set.mem_image_of_mem _ (single_mem_stdSimplex A (Classical.arbitrary A))⟩
      have h2 := hfK k hk
      rw [hf0] at h2
      linarith
  set S := ∑ x, p x with hS
  refine ⟨fun x => p x / S, ⟨fun x => div_nonneg (hpnonneg x) (le_of_lt hSpos), ?_⟩, ?_⟩
  · rw [← Finset.sum_div, ← hS]; field_simp
  · intro a
    have hka : mixedMap cost (Pi.single a (1 : ℝ)) ∈ K :=
      Set.mem_image_of_mem _ (single_mem_stdSimplex A a)
    have h1 : v < f (mixedMap cost (Pi.single a (1 : ℝ))) := hfK _ hka
    have h2 : (mixedMap cost (Pi.single a (1 : ℝ))) = fun x => cost a x := by
      funext x
      show mixedCost cost (Pi.single a (1 : ℝ)) x = cost a x
      rw [mixedCost, Finset.sum_eq_single a]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ a) h
    rw [h2, hfrep] at h1
    have h3 : c * S < ∑ x, cost a x * p x := by linarith
    have h4 : avgCost cost (fun x => p x / S) a = (∑ x, cost a x * p x) / S := by
      rw [avgCost, Finset.sum_div]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [h4, le_div_iff₀ hSpos]
    linarith

lemma randomized_le_distributional [Nonempty A] [Nonempty X] [DecidableEq A] [DecidableEq X]
    (cost : A → X → ℝ) :
    randomizedComplexity cost ≤ distributionalComplexity cost := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨c, hc1, hc2⟩ := exists_between hlt
  obtain ⟨p, hp, hple⟩ := exists_hard_distribution cost hc2
  have h1 : c ≤ ⨅ a, avgCost cost p a := le_ciInf hple
  have h2 : (⨅ a, avgCost cost p a) ≤ distributionalComplexity cost :=
    le_csSup (distributionalSet_bddAbove cost) ⟨p, hp, rfl⟩
  linarith

/-- **Yao's minimax principle**: for a finite cost matrix `cost : A → X → ℝ`, the randomized
complexity (the least worst-case expected cost of a distribution over deterministic algorithms)
equals the distributional complexity (the greatest over input distributions of the least
expected cost of a deterministic algorithm). -/
theorem yao_principle [Nonempty A] [Nonempty X] (cost : A → X → ℝ) :
    randomizedComplexity cost = distributionalComplexity cost := by
  classical
  exact le_antisymm (randomized_le_distributional cost) (distributional_le_randomized cost)

end CS

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

