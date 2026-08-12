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
The header above is a plain block comment rather than a module doc comment (`/-! ... -/`)
because Lean 4 requires `import` commands to be the first commands of a file; a module
doc comment placed before the imports is rejected by the parser.  The text is otherwise
verbatim as requested.

## Contents

For `n : ℕ` we work on the sample space `Finset.range (n+1)` equipped with the uniform
measure, and we consider two `{0,1}`-valued observables:

* `X p = 1` iff `p` is prime;
* `Y p = 1` iff `n - p` is prime (the *reflection* of `X` through the involution
  `p ↦ n - p` of `range (n+1)`).

The empirical covariance of `X` and `Y` is the *Goldbach covariance* `goldbachCov n`.
The main theorem `GoldbachCovarianceTransfer` transfers this analytic quantity into the
purely combinatorial data of the Goldbach problem: the number `goldbachCount n` of
Goldbach representations of `n` and the prime counting function `primeCount n`,
$$\operatorname{Cov}(X,Y) = \frac{r(n)}{n+1} - \left(\frac{\pi(n)}{n+1}\right)^2 .$$
The key input is that the reflection `p ↦ n - p` is an involution of `range (n+1)`, so
`X` and `Y` have the *same* mean, which is what makes the second term a square.

As a consequence we obtain a genuine reduction (`goldbach_of_goldbachCov_gt`): any
lower bound on the Goldbach covariance beating `-(π(n)/(n+1))²` forces `n` to be a sum
of two primes.
-/

open Finset

namespace Brockian.GoldbachComb

/-- Real-valued indicator of a proposition. -/
noncomputable def ind (p : Prop) : ℝ :=
  haveI := Classical.propDecidable p; if p then 1 else 0

theorem ind_eq (p : Prop) [Decidable p] : ind p = if p then 1 else 0 := by
  unfold ind; congr 1

theorem ind_mul (p q : Prop) : ind p * ind q = ind (p ∧ q) := by
  classical
  rw [ind_eq, ind_eq, ind_eq]
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem sum_ind (S : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ∑ x ∈ S, ind (P x) = ((S.filter P).card : ℝ) := by
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ind_eq]
  split <;> simp

/-- Empirical covariance of two observables over a finite sample space with the
uniform measure. -/
noncomputable def cov (S : Finset ℕ) (f g : ℕ → ℝ) : ℝ :=
  (∑ x ∈ S, f x * g x) / S.card -
    ((∑ x ∈ S, f x) / S.card) * ((∑ x ∈ S, g x) / S.card)

/-- `primeCount n = π(n)`, the number of primes `≤ n`. -/
noncomputable def primeCount (n : ℕ) : ℕ := ((range (n + 1)).filter Nat.Prime).card

/-- `goldbachCount n = r(n)`, the number of `p ≤ n` such that both `p` and `n - p`
are prime, i.e. the number of ordered Goldbach representations of `n`. -/
noncomputable def goldbachCount (n : ℕ) : ℕ :=
  ((range (n + 1)).filter (fun p => p.Prime ∧ (n - p).Prime)).card

/-- The Goldbach covariance of `n`: the empirical covariance, over the uniform sample
space `{0, …, n}`, of the primality indicator and its reflection `p ↦ n - p`. -/
noncomputable def goldbachCov (n : ℕ) : ℝ :=
  cov (range (n + 1)) (fun p => ind p.Prime) (fun p => ind (n - p).Prime)

/-- The reflection `p ↦ n - p` is an involution of `range (n+1)`, hence the number of
`p ≤ n` with `n - p` prime equals `π(n)`. -/
theorem card_reflect_prime (n : ℕ) :
    ((range (n + 1)).filter (fun p => (n - p).Prime)).card = primeCount n := by
  classical
  unfold primeCount
  refine Finset.card_bij' (fun p _ => n - p) (fun p _ => n - p) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    exact ⟨by omega, ha.2⟩
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    refine ⟨by omega, ?_⟩
    have h : n - (n - a) = a := by omega
    rw [h]; exact ha.2
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    show n - (n - a) = a
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    show n - (n - a) = a
    omega

theorem sum_primeInd (n : ℕ) :
    ∑ p ∈ range (n + 1), ind p.Prime = (primeCount n : ℝ) := by
  classical
  rw [sum_ind]; rfl

theorem sum_reflectInd (n : ℕ) :
    ∑ p ∈ range (n + 1), ind (n - p).Prime = (primeCount n : ℝ) := by
  classical
  rw [sum_ind, card_reflect_prime]

theorem sum_goldbachInd (n : ℕ) :
    ∑ p ∈ range (n + 1), ind p.Prime * ind (n - p).Prime = (goldbachCount n : ℝ) := by
  classical
  have : ∀ p : ℕ, ind p.Prime * ind (n - p).Prime = ind (p.Prime ∧ (n - p).Prime) :=
    fun p => ind_mul _ _
  simp only [this]
  rw [sum_ind]; rfl

/-- **Goldbach Covariance Transfer.**
The empirical covariance, over the uniform sample space `{0, 1, …, n}`, between the
primality indicator `p ↦ [p prime]` and its reflection `p ↦ [n - p prime]` is exactly
`r(n)/(n+1) - (π(n)/(n+1))²`, where `r(n)` counts the ordered Goldbach representations
of `n` and `π(n)` counts the primes `≤ n`.  Equivalently, the analytic covariance
transfers into the combinatorics of Goldbach representations. -/
theorem GoldbachCovarianceTransfer (n : ℕ) :
    goldbachCov n = (goldbachCount n : ℝ) / (n + 1) - ((primeCount n : ℝ) / (n + 1)) ^ 2 := by
  unfold goldbachCov cov
  rw [sum_goldbachInd, sum_primeInd, sum_reflectInd, Finset.card_range]
  push_cast
  ring

/-- The reflection symmetry of the Goldbach covariance: swapping the two observables
does not change it. -/
theorem goldbachCov_symm (n : ℕ) :
    cov (range (n + 1)) (fun p => ind (n - p).Prime) (fun p => ind p.Prime)
      = goldbachCov n := by
  unfold goldbachCov cov
  rw [sum_primeInd, sum_reflectInd]
  have : ∀ p : ℕ, ind (n - p).Prime * ind p.Prime = ind p.Prime * ind (n - p).Prime :=
    fun p => mul_comm _ _
  simp only [this]

/-- **Conditional reduction.** If the Goldbach covariance of `n` exceeds
`-(π(n)/(n+1))²`, then `n` is a sum of two primes. -/
theorem goldbach_of_goldbachCov_gt (n : ℕ)
    (h : goldbachCov n > -((primeCount n : ℝ) / (n + 1)) ^ 2) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  classical
  rw [GoldbachCovarianceTransfer] at h
  have hpos : (0 : ℝ) < (goldbachCount n : ℝ) / (n + 1) := by linarith
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hc : (0 : ℝ) < (goldbachCount n : ℝ) := (div_pos_iff_of_pos_right hn).mp hpos
  have hz : goldbachCount n ≠ 0 := by
    intro h0
    rw [h0] at hc
    simp at hc
  have hne : ((range (n + 1)).filter (fun p => p.Prime ∧ (n - p).Prime)).Nonempty := by
    rw [← Finset.card_pos]
    exact Nat.pos_of_ne_zero (by simpa [goldbachCount] using hz)
  obtain ⟨p, hp⟩ := hne
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  exact ⟨p, n - p, hp.2.1, hp.2.2, by omega⟩

end Brockian.GoldbachComb

