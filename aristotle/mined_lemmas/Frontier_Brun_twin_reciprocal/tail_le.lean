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

lemma tail_le (hQ : ∀ p ∈ Q, 3 ≤ p) (K : ℕ) :
    ∑ T ∈ Q.powerset.filter (fun T => ¬ T.card ≤ K), ∏ p ∈ T, (2/(p:ℝ))
      ≤ Real.exp (Real.exp 1 * (∑ p ∈ Q, 2/(p:ℝ)) - (K+1)) := by
  classical
  set e := Real.exp 1 with he
  have he0 : (0:ℝ) < e := Real.exp_pos 1
  have hpos : ∀ p ∈ Q, (0:ℝ) < p := by
    intro p hp
    have : (3:ℝ) ≤ p := by exact_mod_cast hQ p hp
    linarith
  have step1 : ∀ T ∈ Q.powerset.filter (fun T => ¬ T.card ≤ K),
      ∏ p ∈ T, (2/(p:ℝ)) ≤ Real.exp (-(K+1)) * ∏ p ∈ T, (2*e/(p:ℝ)) := by
    intro T hT
    have hcard : K + 1 ≤ T.card := by
      have := (Finset.mem_filter.1 hT).2
      omega
    have hTQ : T ⊆ Q := Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1
    have hfac : ∏ p ∈ T, (2*e/(p:ℝ)) = e^T.card * ∏ p ∈ T, (2/(p:ℝ)) := by
      rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun p _ => by ring
    rw [hfac, ← mul_assoc]
    have hprodnn : (0:ℝ) ≤ ∏ p ∈ T, (2/(p:ℝ)) :=
      Finset.prod_nonneg fun p hp => by
        have := hpos p (hTQ hp); positivity
    have hcoef : (1:ℝ) ≤ Real.exp (-(K+1)) * e^T.card := by
      rw [he, ← Real.exp_nat_mul, ← Real.exp_add,
        show -((K:ℝ)+1) + T.card * 1 = (T.card : ℝ) - (K+1) by ring, Real.one_le_exp_iff]
      have : ((K:ℝ)+1) ≤ T.card := by exact_mod_cast hcard
      linarith
    nlinarith
  calc ∑ T ∈ Q.powerset.filter (fun T => ¬ T.card ≤ K), ∏ p ∈ T, (2/(p:ℝ))
      ≤ ∑ T ∈ Q.powerset.filter (fun T => ¬ T.card ≤ K),
          Real.exp (-(K+1)) * ∏ p ∈ T, (2*e/(p:ℝ)) := Finset.sum_le_sum step1
    _ = Real.exp (-(K+1)) *
          ∑ T ∈ Q.powerset.filter (fun T => ¬ T.card ≤ K), ∏ p ∈ T, (2*e/(p:ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-(K+1)) * ∑ T ∈ Q.powerset, ∏ p ∈ T, (2*e/(p:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro T hT _
        exact Finset.prod_nonneg fun p hp => by
          have := hpos p (Finset.mem_powerset.1 hT hp); positivity
    _ = Real.exp (-(K+1)) * ∏ p ∈ Q, (1 + 2*e/(p:ℝ)) := by
        congr 1
        have h := Finset.prod_add (fun p : ℕ => (2*e/(p:ℝ))) (fun _ => (1:ℝ)) Q
        simp only [Finset.prod_const_one, mul_one] at h
        rw [show (fun p : ℕ => (2*e/(p:ℝ)) + 1) = (fun p : ℕ => 1 + 2*e/(p:ℝ)) by
          funext p; ring] at h
        rw [h]
    _ ≤ Real.exp (-(K+1)) * Real.exp (e * ∑ p ∈ Q, 2/(p:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        rw [Finset.mul_sum, Real.exp_sum]
        apply Finset.prod_le_prod
        · intro p hp
          have := hpos p hp; positivity
        · intro p _
          have h1 := Real.add_one_le_exp (e * (2/(p:ℝ)))
          have h2 : e * (2/(p:ℝ)) = 2*e/(p:ℝ) := by ring
          rw [h2] at h1 ⊢
          linarith
    _ = Real.exp (e * (∑ p ∈ Q, 2/(p:ℝ)) - (K+1)) := by
        rw [← Real.exp_add]; ring_nf

/-- The truncated main term of the sieve. -/
