import Mathlib
/-!
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian

/-- Telescoping partial-sum estimate: for `N ≥ 1`,
`∑_{i < n} 1/(i+N)^2 ≤ 1/(N - 1/2) - 1/(N + n - 1/2)`.
Proved by induction on `n`, using `1/x^2 ≤ 1/(x - 1/2) - 1/(x + 1/2)`. -/
lemma partial_sum_inv_sq_shift_le (N : ℕ) (hN : 1 ≤ N) (n : ℕ) :
    ∑ i ∈ Finset.range n, (((i : ℝ) + N) ^ 2)⁻¹
      ≤ 1 / ((N : ℝ) - 1 / 2) - 1 / ((N : ℝ) + n - 1 / 2) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    set x : ℝ := (N : ℝ) + n with hx
    have hx1 : (1 : ℝ) ≤ x := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      simp only [hx]; linarith
    have hpos1 : (0 : ℝ) < x - 1 / 2 := by linarith
    have hpos2 : (0 : ℝ) < x + 1 / 2 := by linarith
    have hpos3 : (0 : ℝ) < x ^ 2 - 1 / 4 := by nlinarith
    have key : (x ^ 2)⁻¹ ≤ 1 / (x - 1 / 2) - 1 / (x + 1 / 2) := by
      have heq : 1 / (x - 1 / 2) - 1 / (x + 1 / 2) = 1 / (x ^ 2 - 1 / 4) := by
        rw [div_sub_div _ _ (ne_of_gt hpos1) (ne_of_gt hpos2), div_eq_div_iff
          (by positivity) (ne_of_gt hpos3)]
        ring
      rw [heq, inv_eq_one_div]
      apply one_div_le_one_div_of_le
      · nlinarith
      · nlinarith
    have hcast : ((N : ℝ) + (↑(n + 1) : ℝ) - 1 / 2) = x + 1 / 2 := by
      push_cast; simp only [hx]; ring
    rw [hcast]
    have hxn : ((n : ℝ) + (N : ℝ)) = x := by simp only [hx]; ring
    rw [hxn]
    linarith

/-- The shifted inverse-square series is summable. -/
lemma summable_inv_sq_shift (N : ℕ) :
    Summable fun i : ℕ => (((i : ℝ) + N) ^ 2)⁻¹ := by
  have h : Summable fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ :=
    Real.summable_nat_pow_inv.2 (by norm_num)
  have h2 := (summable_nat_add_iff (f := fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) N).2 h
  simpa [Nat.cast_add] using h2

/-- Effective tail bound for the inverse-square series: for `N ≥ 1`,
`∑_{i ≥ 0} 1/(i+N)^2 ≤ 2/N`. -/
lemma tsum_inv_sq_shift_le (N : ℕ) (hN : 1 ≤ N) :
    ∑' i : ℕ, (((i : ℝ) + N) ^ 2)⁻¹ ≤ 2 / N := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  refine (summable_inv_sq_shift N).tsum_le_of_sum_range_le (fun n => ?_)
  refine (partial_sum_inv_sq_shift_le N hN n).trans ?_
  have hpos : (0 : ℝ) < (N : ℝ) + n - 1 / 2 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h1 : 1 / ((N : ℝ) - 1 / 2) ≤ 2 / N := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  have h2 : 0 ≤ 1 / ((N : ℝ) + n - 1 / 2) := le_of_lt (by positivity)
  linarith

/-- **Singular series convergence rate.**

Let `a : ℕ → ℝ` be the local (arithmetic) terms of a singular series, i.e. we think of
`𝔖 = ∑' q, a q`, and assume the standard effective bound `|a q| ≤ C / q ^ 2` for every
modulus `q ≥ 1`. Then the singular series converges absolutely, and the truncation at
level `N` has error at most `2 * C / N`:

`|𝔖 - ∑_{q < N} a q| ≤ 2 * C / N`.

The rate is effective: the implied constant `2 * C` is explicit. -/
theorem SingularSeriesConvergenceRate {a : ℕ → ℝ} {C : ℝ}
    (ha : ∀ q : ℕ, 1 ≤ q → |a q| ≤ C / (q : ℝ) ^ 2) :
    Summable a ∧ ∀ N : ℕ, 1 ≤ N →
      |(∑' q : ℕ, a q) - ∑ q ∈ Finset.range N, a q| ≤ 2 * C / N := by
  have hC : 0 ≤ C := by
    have h := ha 1 le_rfl
    have : |a 1| ≤ C := by simpa using h
    exact le_trans (abs_nonneg _) this
  -- pointwise comparison for the shifted sequence
  have hpt : ∀ N : ℕ, 1 ≤ N → ∀ i : ℕ,
      ‖a (i + N)‖ ≤ C * (((i : ℝ) + N) ^ 2)⁻¹ := by
    intro N hN i
    have h := ha (i + N) (le_trans hN (Nat.le_add_left N i))
    have hcast : ((i + N : ℕ) : ℝ) = (i : ℝ) + N := by push_cast; ring
    rw [hcast] at h
    simpa [Real.norm_eq_abs, div_eq_mul_inv] using h
  have hcomp : ∀ N : ℕ, Summable fun i : ℕ => C * (((i : ℝ) + N) ^ 2)⁻¹ :=
    fun N => (summable_inv_sq_shift N).mul_left C
  have hshift : ∀ N : ℕ, 1 ≤ N → Summable fun i : ℕ => a (i + N) :=
    fun N hN => Summable.of_norm_bounded (hcomp N) (hpt N hN)
  have hsa : Summable a := (summable_nat_add_iff 1).1 (hshift 1 le_rfl)
  refine ⟨hsa, fun N hN => ?_⟩
  have hsplit := hsa.sum_add_tsum_nat_add N
  have hdiff : (∑' q : ℕ, a q) - ∑ q ∈ Finset.range N, a q = ∑' i : ℕ, a (i + N) := by
    rw [← hsplit]; ring
  rw [hdiff]
  have hnorm : ‖∑' i : ℕ, a (i + N)‖ ≤ ∑' i : ℕ, ‖a (i + N)‖ :=
    norm_tsum_le_tsum_norm ((hshift N hN).norm)
  have hle : ∑' i : ℕ, ‖a (i + N)‖ ≤ ∑' i : ℕ, C * (((i : ℝ) + N) ^ 2)⁻¹ :=
    Summable.tsum_le_tsum (hpt N hN) ((hshift N hN).norm) (hcomp N)
  have hfin : ∑' i : ℕ, C * (((i : ℝ) + N) ^ 2)⁻¹ ≤ 2 * C / N := by
    rw [tsum_mul_left]
    have := tsum_inv_sq_shift_le N hN
    calc C * ∑' i : ℕ, (((i : ℝ) + N) ^ 2)⁻¹ ≤ C * (2 / N) := by
          exact mul_le_mul_of_nonneg_left this hC
      _ = 2 * C / N := by ring
  have := hnorm.trans (hle.trans hfin)
  simpa [Real.norm_eq_abs] using this

end Brockian

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

