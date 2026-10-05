/-
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
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
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- Cohomological data attached to a variety over a finite field `𝔽_q`:
the inverse roots (Frobenius eigenvalues) on each cohomology group, together with the
point counts over the extensions `𝔽_{q^m}`, linked by the Grothendieck–Lefschetz trace
formula. -/
structure WeilVariety where
  /-- Cardinality of the base field. -/
  q : ℕ
  /-- The base field has at least two elements. -/
  hq : 2 ≤ q
  /-- Dimension of the variety. -/
  dim : ℕ
  /-- Multiset of inverse roots of Frobenius acting on the `i`-th cohomology group. -/
  frobRoots : ℕ → Multiset ℂ
  /-- `count m` is the number of `𝔽_{q^m}`-rational points. -/
  count : ℕ → ℕ
  /-- Cohomology vanishes above degree `2 * dim`. -/
  vanishing : ∀ i, 2 * dim < i → frobRoots i = 0
  /-- Grothendieck–Lefschetz trace formula. -/
  trace : ∀ m, 1 ≤ m →
    (count m : ℂ) =
      ∑ i ∈ Finset.range (2 * dim + 1),
        (-1) ^ i * (((frobRoots i).map (fun a => a ^ m)).sum)

/-- The Riemann hypothesis for a variety over a finite field: every inverse root of
Frobenius on the `i`-th cohomology group has archimedean absolute value `q ^ (i / 2)`. -/

theorem count_estimate_of_riemannHypothesis (W : WeilVariety)
    (hRH : RiemannHypothesis W)
    (htop : W.frobRoots (2 * W.dim) = {((W.q : ℂ)) ^ W.dim})
    (m : ℕ) (hm : 1 ≤ m) :
    ‖(W.count m : ℂ) - ((W.q : ℂ)) ^ (W.dim * m)‖ ≤
      (∑ i ∈ Finset.range (2 * W.dim), (Multiset.card (W.frobRoots i) : ℝ)) *
        (W.q : ℝ) ^ (((2 * W.dim - 1 : ℕ) : ℝ) * m / 2) := by
  have hq1 : (1 : ℝ) ≤ (W.q : ℝ) := by
    have := W.hq
    exact_mod_cast le_trans (by norm_num) this
  have hq0 : (0 : ℝ) ≤ (W.q : ℝ) := le_trans zero_le_one hq1
  set d := W.dim with hd
  set Q : ℝ := (W.q : ℝ) ^ (((2 * d - 1 : ℕ) : ℝ) * m / 2) with hQ
  -- rewrite the difference as the alternating sum over degrees below the top one
  have htopterm : (((W.frobRoots (2 * d)).map (fun a => a ^ m)).sum) = ((W.q : ℂ)) ^ (d * m) := by
    rw [htop]
    simp [pow_mul]
  have key : (W.count m : ℂ) - ((W.q : ℂ)) ^ (d * m)
      = ∑ i ∈ Finset.range (2 * d), (-1 : ℂ) ^ i * (((W.frobRoots i).map (fun a => a ^ m)).sum) := by
    rw [W.trace m hm, Finset.sum_range_succ, htopterm]
    have hsign : ((-1 : ℂ)) ^ (2 * d) = 1 := by
      rw [pow_mul]; simp
    rw [hsign, one_mul]
    ring
  rw [key]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ i ∈ Finset.range (2 * d),
      ‖(-1 : ℂ) ^ i * (((W.frobRoots i).map (fun a => a ^ m)).sum)‖
        ≤ (Multiset.card (W.frobRoots i) : ℝ) * Q := by
    intro i hi
    have hi2d : i ≤ 2 * d := le_of_lt (Finset.mem_range.mp hi)
    have hbound : ∀ a ∈ W.frobRoots i, ‖a‖ ≤ (W.q : ℝ) ^ ((i : ℝ) / 2) :=
      fun a ha => le_of_eq (hRH i hi2d a ha)
    have h1 : ‖(((W.frobRoots i).map (fun a => a ^ m)).sum)‖
        ≤ (Multiset.card (W.frobRoots i) : ℝ) * ((W.q : ℝ) ^ ((i : ℝ) / 2)) ^ m :=
      multiset_pow_sum_norm_le _ _ m hbound
    have h2 : ((W.q : ℝ) ^ ((i : ℝ) / 2)) ^ m = (W.q : ℝ) ^ (((i : ℝ) / 2) * m) := by
      rw [← Real.rpow_natCast ((W.q : ℝ) ^ ((i : ℝ) / 2)) m, ← Real.rpow_mul hq0]
    have h3 : ((i : ℝ) / 2) * m ≤ ((2 * d - 1 : ℕ) : ℝ) * m / 2 := by
      have hile : (i : ℝ) ≤ ((2 * d - 1 : ℕ) : ℝ) := by
        have : i ≤ 2 * d - 1 := by
          have := Finset.mem_range.mp hi
          omega
        exact_mod_cast this
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hile hm0]
    have h4 : (W.q : ℝ) ^ (((i : ℝ) / 2) * m) ≤ Q :=
      Real.rpow_le_rpow_of_exponent_le hq1 h3
    calc ‖(-1 : ℂ) ^ i * (((W.frobRoots i).map (fun a => a ^ m)).sum)‖
        = ‖(((W.frobRoots i).map (fun a => a ^ m)).sum)‖ := by
          simp
      _ ≤ (Multiset.card (W.frobRoots i) : ℝ) * ((W.q : ℝ) ^ ((i : ℝ) / 2)) ^ m := h1
      _ ≤ (Multiset.card (W.frobRoots i) : ℝ) * Q := by
          have hcard : (0 : ℝ) ≤ (Multiset.card (W.frobRoots i) : ℝ) := by positivity
          rw [h2]
          exact mul_le_mul_of_nonneg_left h4 hcard
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]

/-- The Weil Riemann hypothesis (Deligne): formalized statement, together with a proof of the
projective-space base case and of the square-root point-count estimate that the Riemann
hypothesis implies. -/
