/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Statement: Yao's minimax principle relates randomized and distributional complexity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Statement: Yao's minimax principle relates randomized and distributional complexity.
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

variable {A I : Type*} [Fintype A] [Nonempty A] [Fintype I] [Nonempty I]

/-- The expected cost of the randomized algorithm given by the mixed strategy `p`
(a distribution over the deterministic algorithms `A`) on the worst-case input. -/

lemma weak_duality (C : A → I → ℝ) {p : A → ℝ} (hp : p ∈ stdSimplex ℝ A)
    {q : I → ℝ} (hq : q ∈ stdSimplex ℝ I) :
    distributionalCost C q ≤ randomizedCost C p := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hq0, hq1⟩ := hq
  have h1 : distributionalCost C q ≤ ∑ a, p a * (∑ i, q i * C a i) := by
    have h : ∑ a, p a * distributionalCost C q ≤ ∑ a, p a * (∑ i, q i * C a i) :=
      Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (distributionalCost_le_expect C q a) (hp0 a)
    rwa [← Finset.sum_mul, hp1, one_mul] at h
  refine h1.trans ?_
  have hswap : ∑ a, p a * (∑ i, q i * C a i) = ∑ i, q i * (∑ a, p a * C a i) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring
  rw [hswap]
  have h : ∑ i, q i * (∑ a, p a * C a i) ≤ ∑ i, q i * randomizedCost C p :=
    Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (expect_le_randomizedCost C p i) (hq0 i)
  rwa [← Finset.sum_mul, hq1, one_mul] at h

