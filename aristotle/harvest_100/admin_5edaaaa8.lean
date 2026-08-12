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

/-
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators

namespace Brockian
namespace GoldbachComb

/-- The set of Goldbach summands of `n`: primes `p ≤ n` such that `n - p` is also prime.
Thus `p ∈ goldbachSet n` exactly when `p + (n - p) = n` is a Goldbach decomposition of `n`. -/
def goldbachSet (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))

lemma mem_goldbachSet {n p : ℕ} :
    p ∈ goldbachSet n ↔ p ≤ n ∧ Nat.Prime p ∧ Nat.Prime (n - p) := by
  classical
  simp [goldbachSet]

/-- The reflection `p ↦ n - p` maps the Goldbach set of `n` to itself. -/
lemma reflect_mem_goldbachSet {n p : ℕ} (hp : p ∈ goldbachSet n) :
    n - p ∈ goldbachSet n := by
  rw [mem_goldbachSet] at hp ⊢
  obtain ⟨hle, hp1, hp2⟩ := hp
  refine ⟨Nat.sub_le _ _, hp2, ?_⟩
  rwa [Nat.sub_sub_self hle]

/-- The empirical mean of `f` over a finite set of naturals. -/
noncomputable def mean (s : Finset ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ p ∈ s, f p) / s.card

/-- The empirical covariance of `f` and `g` over a finite set of naturals. -/
noncomputable def cov (s : Finset ℕ) (f g : ℕ → ℝ) : ℝ :=
  mean s (fun p => f p * g p) - mean s f * mean s g

lemma mean_congr {s : Finset ℕ} {f g : ℕ → ℝ} (h : ∀ p ∈ s, f p = g p) :
    mean s f = mean s g := by
  unfold mean
  rw [Finset.sum_congr rfl h]

lemma cov_congr {s : Finset ℕ} {f₁ f₂ g₁ g₂ : ℕ → ℝ}
    (hf : ∀ p ∈ s, f₁ p = f₂ p) (hg : ∀ p ∈ s, g₁ p = g₂ p) :
    cov s f₁ g₁ = cov s f₂ g₂ := by
  unfold cov
  rw [mean_congr (fun p hp => by rw [hf p hp, hg p hp]), mean_congr hf, mean_congr hg]

/-- Sums over the Goldbach set are invariant under the reflection `p ↦ n - p`. -/
lemma sum_reflect (n : ℕ) (F : ℕ → ℝ) :
    ∑ p ∈ goldbachSet n, F (n - p) = ∑ p ∈ goldbachSet n, F p := by
  refine Finset.sum_nbij' (i := fun p => n - p) (j := fun p => n - p)
    (fun a ha => reflect_mem_goldbachSet ha) (fun a ha => reflect_mem_goldbachSet ha)
    (fun a ha => ?_) (fun a ha => ?_) (fun a _ => rfl)
  · exact Nat.sub_sub_self (mem_goldbachSet.mp ha).1
  · exact Nat.sub_sub_self (mem_goldbachSet.mp ha).1

/-- Means over the Goldbach set are invariant under the reflection `p ↦ n - p`. -/
lemma mean_reflect (n : ℕ) (F : ℕ → ℝ) :
    mean (goldbachSet n) (fun p => F (n - p)) = mean (goldbachSet n) F := by
  unfold mean
  rw [sum_reflect]

/--
**Goldbach Covariance Transfer.**

For every `n` and every pair of real-valued statistics `f, g` on the natural numbers, the
empirical covariance of `f` and `g` over the Goldbach summands of `n` is unchanged when both
statistics are transferred to the Goldbach partner, i.e. evaluated at `n - p` instead of `p`.
-/
theorem GoldbachCovarianceTransfer (n : ℕ) (f g : ℕ → ℝ) :
    cov (goldbachSet n) (fun p => f (n - p)) (fun p => g (n - p))
      = cov (goldbachSet n) f g := by
  unfold cov
  rw [mean_reflect n f, mean_reflect n g]
  congr 1
  exact mean_reflect n (fun p => f p * g p)

/-- Replacing the first argument `f` of the covariance by `c - f` negates the covariance. -/
lemma cov_const_sub (s : Finset ℕ) (c : ℝ) (f h : ℕ → ℝ) :
    cov s (fun p => c - f p) h = - cov s f h := by
  rcases Nat.eq_zero_or_pos s.card with hc | hc
  · have hs : s = ∅ := Finset.card_eq_zero.mp hc
    simp [cov, mean, hs]
  · have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
    have h1 : mean s (fun p => (c - f p) * h p)
        = c * mean s h - mean s (fun p => f p * h p) := by
      unfold mean
      rw [mul_div_assoc', div_sub_div_same]
      congr 1
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring
    have h2 : mean s (fun p => c - f p) = c - mean s f := by
      unfold mean
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      field_simp
    unfold cov
    rw [h1, h2]
    ring

/--
**Goldbach anticovariance.**

A consequence of the covariance transfer: the covariance of the summand `p` with any statistic
of its Goldbach partner `n - p` is the negative of the covariance of `p` with that statistic
of `p` itself.
-/
theorem GoldbachPartnerAnticovariance (n : ℕ) (g : ℕ → ℝ) :
    cov (goldbachSet n) (fun p => (p : ℝ)) (fun p => g (n - p))
      = - cov (goldbachSet n) (fun p => (p : ℝ)) g := by
  have key := GoldbachCovarianceTransfer n (fun p => (p : ℝ)) g
  have hrw : cov (goldbachSet n) (fun p => ((n - p : ℕ) : ℝ)) (fun p => g (n - p))
      = cov (goldbachSet n) (fun p => (n : ℝ) - (p : ℝ)) (fun p => g (n - p)) := by
    refine cov_congr (fun p hp => ?_) (fun _ _ => rfl)
    exact Nat.cast_sub (mem_goldbachSet.mp hp).1
  rw [hrw, cov_const_sub] at key
  linarith [key]

/-- Sanity check: the Goldbach summands of `10` are `3, 5, 7`, so the covariance above is
taken over a genuinely nonempty sample. -/
lemma goldbachSet_ten : goldbachSet 10 = {3, 5, 7} := by decide

end GoldbachComb
end Brockian

