/-
# Entropy Concave
Category: Chemistry
Target: Chem.entropy_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Real Finset

/-- The Gibbs entropy of a (finite) probability vector `p`: `S(p) = -∑ i, p i * log (p i)`,
written using Mathlib's `Real.negMulLog x = -x * log x` (so that the `p i = 0` terms vanish). -/
noncomputable def entropy {n : ℕ} (p : Fin n → ℝ) : ℝ := ∑ i, Real.negMulLog (p i)

lemma entropy_eq {n : ℕ} (p : Fin n → ℝ) : entropy p = -∑ i, p i * Real.log (p i) := by
  simp [entropy, Real.negMulLog, Finset.sum_neg_distrib]

/-- **Gibbs entropy is concave**: `p ↦ -∑ i, p i * log (p i)` is a concave function on the set of
nonnegative vectors (in particular on the probability simplex).

The one–dimensional ingredient is `Real.concaveOn_negMulLog : ConcaveOn ℝ (Set.Ici 0) negMulLog`;
concavity of the sum follows termwise. -/
theorem entropy_concave (n : ℕ) :
    ConcaveOn ℝ {p : Fin n → ℝ | ∀ i, 0 ≤ p i} entropy := by
  constructor
  · intro x hx y hy a b ha hb _ i
    have hxi := hx i
    have hyi := hy i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    positivity
  · intro x hx y hy a b ha hb hab
    simp only [entropy, smul_eq_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    exact Real.concaveOn_negMulLog.2 (hx i) (hy i) ha hb hab

/-- **Strict** concavity of the Gibbs entropy on the set of nonnegative vectors, from
`Real.strictConcaveOn_negMulLog`. -/
theorem entropy_strictConcave (n : ℕ) :
    StrictConcaveOn ℝ {p : Fin n → ℝ | ∀ i, 0 ≤ p i} entropy := by
  refine ⟨(entropy_concave n).1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := Function.ne_iff.1 hxy
  simp only [entropy, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_lt_sum (fun i _ => Real.concaveOn_negMulLog.2 (hx i) (hy i) ha.le hb.le hab)
    ⟨j, Finset.mem_univ j, Real.strictConcaveOn_negMulLog.2 (hx j) (hy j) hj ha hb hab⟩

/-- Concavity of the Gibbs entropy restricted to the probability simplex. -/
theorem entropy_concaveOn_simplex (n : ℕ) :
    ConcaveOn ℝ {p : Fin n → ℝ | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1} entropy := by
  refine (entropy_concave n).subset (fun p hp => hp.1) ?_
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => by have := hx.1 i; have := hy.1 i; dsimp; positivity, ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hx.2, hy.2, mul_one, hab]

end Chem

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

