import Mathlib
import RequestProject.Brun.Final

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede every other command, including module
-- doc comments, so the required header comment appears immediately after the imports.)

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The summand is `1/n` whenever `n` and `n + 2` are both prime, and `0` otherwise; the value of
its sum is Brun's constant.  Convergence is proved from scratch by a Brun pure sieve; see the
development in `RequestProject/Brun/`. -/

lemma sum_squarefree_le_prod (n : ℕ) :
    ∑ a ∈ (Icc 1 n).filter Squarefree, (1 : ℝ) / a ≤
      ∏ p ∈ Nat.primesBelow (n + 1), (1 + (1 : ℝ) / p) := by
  classical
  set S := (Icc 1 n).filter Squarefree with hS
  set P := Nat.primesBelow (n+1) with hP
  have hmem : ∀ a ∈ S, 1 ≤ a ∧ a ≤ n ∧ Squarefree a := by
    intro a ha
    simp only [hS, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨ha.1.1, ha.1.2, ha.2⟩
  have hprod : ∀ a ∈ S, ∏ p ∈ a.primeFactors, (1:ℝ)/p = 1/a := by
    intro a ha
    obtain ⟨h1, h2, h3⟩ := hmem a ha
    have h4 : ∏ p ∈ a.primeFactors, p = a := Nat.prod_primeFactors_of_squarefree h3
    rw [Finset.prod_div_distrib, ← Nat.cast_prod, h4]
    simp
  have hinj : Set.InjOn Nat.primeFactors (S : Set ℕ) := by
    intro x hx y hy h
    obtain ⟨_, _, h3⟩ := hmem x hx
    obtain ⟨_, _, h3'⟩ := hmem y hy
    rw [← Nat.prod_primeFactors_of_squarefree h3, ← Nat.prod_primeFactors_of_squarefree h3', h]
  have hsub : S.image Nat.primeFactors ⊆ P.powerset := by
    intro T hT
    simp only [Finset.mem_image] at hT
    obtain ⟨a, ha, rfl⟩ := hT
    obtain ⟨h1, h2, h3⟩ := hmem a ha
    rw [Finset.mem_powerset]
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    rw [hP, Nat.mem_primesBelow]
    exact ⟨lt_of_le_of_lt (Nat.le_of_dvd (by omega) hp.2.1) (by omega), hp.1⟩
  calc ∑ a ∈ S, (1:ℝ)/a = ∑ a ∈ S, ∏ p ∈ a.primeFactors, (1:ℝ)/p :=
        (Finset.sum_congr rfl hprod).symm
    _ = ∑ T ∈ S.image Nat.primeFactors, ∏ p ∈ T, (1:ℝ)/p :=
        (Finset.sum_image (f := fun T : Finset ℕ => ∏ p ∈ T, (1:ℝ)/(p:ℝ)) hinj).symm
    _ ≤ ∑ T ∈ P.powerset, ∏ p ∈ T, (1:ℝ)/p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro T _ _
        positivity
    _ = ∏ p ∈ P, ((1:ℝ)/p + 1) := by rw [Finset.prod_add]; simp
    _ = ∏ p ∈ P, (1 + (1:ℝ)/p) := by simp [add_comm]

/-- `∏ (1 + 1/p) ≤ exp (∑ 1/p)`. -/
