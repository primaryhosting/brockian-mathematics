/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
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

set_option grind.warning false

/-!
## Overview

Mathlib has no minimax theorem, so the result is proved from scratch.  The only nontrivial
input from Mathlib is the separation theorem `geometric_hahn_banach_compact_closed`
(`Mathlib/Analysis/LocallyConvex/Separation.lean`), which is used to prove Ville's theorem of
the alternative (`CS.ville_alternative`).  Yao's principle then follows by applying the
alternative to the shifted cost matrix `cost a x - v`, where `v` is the randomized complexity,
together with weak duality (`CS.distCost_le_randCost`).
-/

namespace CS

section Orthant

variable {A : Type*}

/-- The nonnegative orthant in `A → ℝ` is convex. -/
lemma convex_nonneg_orthant : Convex ℝ {y : A → ℝ | ∀ a, 0 ≤ y a} := by
  intro y hy z hz s t hs ht _ a
  exact add_nonneg (mul_nonneg hs (hy a)) (mul_nonneg ht (hz a))

/-- The nonnegative orthant in `A → ℝ` is closed. -/
lemma isClosed_nonneg_orthant : IsClosed {y : A → ℝ | ∀ a, 0 ≤ y a} := by
  have h : {y : A → ℝ | ∀ a, 0 ≤ y a} = ⋂ a : A, {y : A → ℝ | 0 ≤ y a} := by
    ext y; simp
  rw [h]
  exact isClosed_iInter fun a => isClosed_le continuous_const (continuous_apply a)

end Orthant

section Alternative

variable {A X : Type*} [Fintype A] [Fintype X]

/-- The expected-payoff map associated to a cost matrix `M`: a mixed strategy `q` over the
columns `X` is sent to the vector of expected payoffs, indexed by the rows `A`. -/
noncomputable def payoffMap (M : A → X → ℝ) : (X → ℝ) →ₗ[ℝ] (A → ℝ) where
  toFun q a := ∑ x, q x * M a x
  map_add' q r := by
    funext a; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c q := by
    funext a; simp [Finset.mul_sum, mul_assoc, smul_eq_mul]

omit [Fintype A] in
lemma payoffMap_apply (M : A → X → ℝ) (q : X → ℝ) (a : A) :
    payoffMap M q a = ∑ x, q x * M a x := rfl

/-- **Ville's theorem of the alternative** for a real matrix `M`: either there is a mixed
strategy `p` over the rows making all column payoffs strictly negative, or there is a mixed
strategy `q` over the columns making all row payoffs nonnegative. -/
theorem ville_alternative [Nonempty X] (M : A → X → ℝ) :
    (∃ p ∈ stdSimplex ℝ A, ∀ x, ∑ a, p a * M a x < 0) ∨
      (∃ q ∈ stdSimplex ℝ X, ∀ a, 0 ≤ ∑ x, q x * M a x) := by
  by_cases h : ∃ q ∈ stdSimplex ℝ X, ∀ a, 0 ≤ ∑ x, q x * M a x
  · exact Or.inr h
  left
  push_neg at h
  set K : Set (A → ℝ) := payoffMap M '' stdSimplex ℝ X
  set T : Set (A → ℝ) := {y : A → ℝ | ∀ a, 0 ≤ y a}
  have hKconv : Convex ℝ K := (convex_stdSimplex ℝ X).linear_image _
  have hKcomp : IsCompact K := by
    refine (isCompact_stdSimplex X).image ?_
    apply continuous_pi
    intro a
    exact continuous_finset_sum _ fun x _ => (continuous_apply x).mul continuous_const
  have hdisj : Disjoint K T := by
    rw [Set.disjoint_left]
    rintro y ⟨q, hq, rfl⟩ hyT
    obtain ⟨a, ha⟩ := h q hq
    exact absurd (hyT a) (not_le.2 ha)
  obtain ⟨f, u, v, hfK, huv, hfT⟩ :=
    geometric_hahn_banach_compact_closed hKconv hKcomp convex_nonneg_orthant
      isClosed_nonneg_orthant hdisj
  -- `v < f 0 = 0`
  have hv0 : v < 0 := by
    have := hfT 0 (by intro a; simp)
    simpa using this
  have hu0 : u < 0 := lt_trans huv hv0
  -- coefficients of `f`
  set c : A → ℝ := fun a => f (fun j => if a = j then (1 : ℝ) else 0) with hc
  have hfy : ∀ y : A → ℝ, f y = ∑ a, y a * c a := by
    intro y
    have := LinearMap.pi_apply_eq_sum_univ (f : (A → ℝ) →ₗ[ℝ] ℝ) y
    simpa [hc, smul_eq_mul] using this
  have hcnonneg : ∀ a, 0 ≤ c a := by
    intro a
    by_contra hneg
    push_neg at hneg
    set t : ℝ := v / c a with ht
    have htpos : 0 < t := div_pos_of_neg_of_neg hv0 hneg
    have hmem : (t • fun j => if a = j then (1 : ℝ) else 0) ∈ T := by
      intro b
      by_cases hb : a = b <;> simp [hb, htpos.le]
    have := hfT _ hmem
    rw [map_smul] at this
    simp only [smul_eq_mul] at this
    rw [ht, div_mul_cancel₀ _ (ne_of_lt hneg)] at this
    exact lt_irrefl v this
  have hKne : K.Nonempty := by
    obtain ⟨q, hq⟩ : (stdSimplex ℝ X).Nonempty := Set.Nonempty.of_subtype
    exact ⟨payoffMap M q, q, hq, rfl⟩
  have hSpos : 0 < ∑ a, c a := by
    rcases lt_or_eq_of_le (Finset.sum_nonneg fun a _ => hcnonneg a) with hlt | heq
    · exact hlt
    · exfalso
      have hallzero : ∀ a, c a = 0 := by
        intro a
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hcnonneg a)).1 heq.symm
        exact this a (Finset.mem_univ a)
      obtain ⟨y, hy⟩ := hKne
      have hzero : f y = 0 := by rw [hfy y]; simp [hallzero]
      have hylt := hfK y hy
      rw [hzero] at hylt
      exact absurd hylt (not_lt.2 hu0.le)
  refine ⟨fun a => c a / (∑ a', c a'), ⟨fun a => div_nonneg (hcnonneg a) hSpos.le, ?_⟩, ?_⟩
  · rw [← Finset.sum_div, div_self (ne_of_gt hSpos)]
  · intro x
    have hq : (fun x' => if x' = x then (1 : ℝ) else 0) ∈ stdSimplex ℝ X :=
      ⟨fun x' => by positivity, by simp⟩
    have hmem : payoffMap M (fun x' => if x' = x then (1 : ℝ) else 0) ∈ K :=
      Set.mem_image_of_mem _ hq
    have hlt := hfK _ hmem
    have hval : f (payoffMap M (fun x' => if x' = x then (1 : ℝ) else 0)) = ∑ a, c a * M a x := by
      rw [hfy]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [payoffMap_apply]
      simp [Finset.sum_ite_eq', mul_comm]
    rw [hval] at hlt
    have hneg : ∑ a, c a * M a x < 0 := lt_trans hlt hu0
    have : ∑ a, c a / (∑ a', c a') * M a x = (∑ a, c a * M a x) / (∑ a', c a') := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [this]
    exact div_neg_of_neg_of_pos hneg hSpos

end Alternative

section Yao

variable {A X : Type*} [Fintype A] [Fintype X] [Nonempty A] [Nonempty X]

private lemma ciSup_lt_of_forall_lt {ι : Type*} [Fintype ι] [Nonempty ι] {g : ι → ℝ} {c : ℝ}
    (hg : ∀ i, g i < c) : (⨆ i, g i) < c := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image (Finset.univ : Finset ι) g Finset.univ_nonempty
  refine lt_of_le_of_lt (ciSup_le fun i => hi₀ i (Finset.mem_univ i)) (hg i₀)

/-- The expected cost of the randomized algorithm `p` on the worst-case input. -/
noncomputable def randCost (cost : A → X → ℝ) (p : A → ℝ) : ℝ :=
  ⨆ x : X, ∑ a, p a * cost a x

/-- The expected cost of the best deterministic algorithm against the input distribution `q`. -/
noncomputable def distCost (cost : A → X → ℝ) (q : X → ℝ) : ℝ :=
  ⨅ a : A, ∑ x, q x * cost a x

omit [Nonempty A] [Nonempty X] in
/-- Weak duality: any input distribution gives a lower bound for any randomized algorithm. -/
theorem distCost_le_randCost (cost : A → X → ℝ) {p : A → ℝ} (hp : p ∈ stdSimplex ℝ A)
    {q : X → ℝ} (hq : q ∈ stdSimplex ℝ X) : distCost cost q ≤ randCost cost p := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hq0, hq1⟩ := hq
  have hbdd : BddBelow (Set.range fun a : A => ∑ x, q x * cost a x) :=
    Finite.bddBelow_range _
  have hbdd' : BddAbove (Set.range fun x : X => ∑ a, p a * cost a x) :=
    Finite.bddAbove_range _
  have h1 : distCost cost q ≤ ∑ a, p a * (∑ x, q x * cost a x) := by
    calc distCost cost q = ∑ a, p a * distCost cost q := by
            rw [← Finset.sum_mul, hp1, one_mul]
      _ ≤ ∑ a, p a * (∑ x, q x * cost a x) := by
            refine Finset.sum_le_sum fun a _ => ?_
            exact mul_le_mul_of_nonneg_left (ciInf_le hbdd a) (hp0 a)
  have h2 : ∑ x, q x * (∑ a, p a * cost a x) ≤ randCost cost p := by
    calc ∑ x, q x * (∑ a, p a * cost a x)
        ≤ ∑ x, q x * randCost cost p := by
          refine Finset.sum_le_sum fun x _ => ?_
          exact mul_le_mul_of_nonneg_left (le_ciSup hbdd' x) (hq0 x)
      _ = randCost cost p := by rw [← Finset.sum_mul, hq1, one_mul]
  have hswap : ∑ a, p a * (∑ x, q x * cost a x) = ∑ x, q x * (∑ a, p a * cost a x) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a _ => by ring
  linarith [h1, h2, hswap.le, hswap.ge]

private lemma bddBelow_randCost (cost : A → X → ℝ) :
    BddBelow (Set.range fun p : stdSimplex ℝ A => randCost cost p) := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty X›
  set m : ℝ := Finset.univ.inf' (Finset.univ_nonempty) (fun z : A × X => cost z.1 z.2) with hm
  refine ⟨m, ?_⟩
  rintro r ⟨p, rfl⟩
  have hp0 : ∀ a, 0 ≤ (p : A → ℝ) a := p.2.1
  have hp1 : ∑ a, (p : A → ℝ) a = 1 := p.2.2
  have hbdd' : BddAbove (Set.range fun x : X => ∑ a, (p : A → ℝ) a * cost a x) :=
    Finite.bddAbove_range _
  have : m ≤ ∑ a, (p : A → ℝ) a * cost a x₀ := by
    calc m = ∑ a, (p : A → ℝ) a * m := by rw [← Finset.sum_mul, hp1, one_mul]
      _ ≤ ∑ a, (p : A → ℝ) a * cost a x₀ := by
          refine Finset.sum_le_sum fun a _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (hp0 a)
          exact Finset.inf'_le (fun z : A × X => cost z.1 z.2) (Finset.mem_univ (a, x₀))
  exact le_trans this (le_ciSup hbdd' x₀)

private lemma bddAbove_distCost (cost : A → X → ℝ) :
    BddAbove (Set.range fun q : stdSimplex ℝ X => distCost cost q) := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty A›
  set Mx : ℝ := Finset.univ.sup' (Finset.univ_nonempty) (fun z : A × X => cost z.1 z.2) with hMx
  refine ⟨Mx, ?_⟩
  rintro r ⟨q, rfl⟩
  have hq0 : ∀ x, 0 ≤ (q : X → ℝ) x := q.2.1
  have hq1 : ∑ x, (q : X → ℝ) x = 1 := q.2.2
  have hbdd : BddBelow (Set.range fun a : A => ∑ x, (q : X → ℝ) x * cost a x) :=
    Finite.bddBelow_range _
  have : ∑ x, (q : X → ℝ) x * cost a₀ x ≤ Mx := by
    calc ∑ x, (q : X → ℝ) x * cost a₀ x ≤ ∑ x, (q : X → ℝ) x * Mx := by
          refine Finset.sum_le_sum fun x _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (hq0 x)
          exact Finset.le_sup' (fun z : A × X => cost z.1 z.2) (Finset.mem_univ (a₀, x))
      _ = Mx := by rw [← Finset.sum_mul, hq1, one_mul]
  exact le_trans (ciInf_le hbdd a₀) this

/-- **Existence of a hard input distribution.**  There is an input distribution `q` whose
distributional complexity equals the randomized complexity; in particular `q` certifies the
optimal lower bound for every randomized algorithm. -/
theorem exists_hard_distribution (cost : A → X → ℝ) :
    ∃ q ∈ stdSimplex ℝ X,
      (⨅ p : stdSimplex ℝ A, randCost cost p) = distCost cost q ∧
        ∀ p ∈ stdSimplex ℝ A, distCost cost q ≤ randCost cost p := by
  classical
  set v : ℝ := ⨅ p : stdSimplex ℝ A, randCost cost p
  have hbddI := bddBelow_randCost cost
  rcases ville_alternative (A := A) (X := X) (fun a x => cost a x - v) with ⟨p, hp, hpx⟩ | h
  · exfalso
    have hstrict : ∀ x, ∑ a, p a * cost a x < v := by
      intro x
      have hx := hpx x
      have hrw : ∑ a, p a * (cost a x - v) = (∑ a, p a * cost a x) - v := by
        simp only [mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, one_mul]
      linarith [hrw ▸ hx]
    have hlt : randCost cost p < v := ciSup_lt_of_forall_lt hstrict
    have hge : v ≤ randCost cost p := ciInf_le hbddI (⟨p, hp⟩ : stdSimplex ℝ A)
    exact absurd hge (not_le.2 hlt)
  · obtain ⟨q, hq, hqa⟩ := h
    have hall : ∀ a, v ≤ ∑ x, q x * cost a x := by
      intro a
      have ha := hqa a
      have hrw : ∑ x, q x * (cost a x - v) = (∑ x, q x * cost a x) - v := by
        simp only [mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hq.2, one_mul]
      linarith [hrw ▸ ha]
    have h1 : v ≤ distCost cost q := le_ciInf hall
    have h2 : ∀ p ∈ stdSimplex ℝ A, distCost cost q ≤ randCost cost p :=
      fun p hp => distCost_le_randCost cost hp hq
    refine ⟨q, hq, le_antisymm h1 ?_, h2⟩
    exact le_ciInf fun p => h2 p p.2

/-- **Yao's minimax principle**.  For a finite set `A` of deterministic algorithms, a finite
set `X` of inputs and a cost matrix `cost`, the optimal worst-case expected cost of a
randomized algorithm (a distribution over `A`) equals the optimal, over input distributions,
of the best deterministic algorithm's expected cost. -/
theorem yao_principle (cost : A → X → ℝ) :
    (⨅ p : stdSimplex ℝ A, ⨆ x : X, ∑ a, (p : A → ℝ) a * cost a x) =
      ⨆ q : stdSimplex ℝ X, ⨅ a : A, ∑ x, (q : X → ℝ) x * cost a x := by
  show (⨅ p : stdSimplex ℝ A, randCost cost p) = ⨆ q : stdSimplex ℝ X, distCost cost q
  obtain ⟨q, hq, hqv, -⟩ := exists_hard_distribution cost
  refine le_antisymm ?_ ?_
  · rw [hqv]
    exact le_ciSup (bddAbove_distCost cost) (⟨q, hq⟩ : stdSimplex ℝ X)
  · exact ciSup_le fun q' => le_ciInf fun p => distCost_le_randCost cost p.2 q'.2

end Yao

end CS

