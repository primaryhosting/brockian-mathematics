/-
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset

/-- Telescoping tail estimate: for `Q ≥ 1`,
`∑_{i < n} 1/(i+Q+1)^2 ≤ 1/Q - 1/(Q+n)`. -/
lemma sum_range_inv_sq_shift_le (Q : ℕ) (hQ : 1 ≤ Q) (n : ℕ) :
    ∑ i ∈ range n, (1 : ℝ) / ((i : ℝ) + Q + 1) ^ 2 ≤ 1 / (Q : ℝ) - 1 / ((Q : ℝ) + n) := by
  have hQ' : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : (0 : ℝ) < (Q : ℝ) + n := by positivity
      have h2 : (0 : ℝ) < (Q : ℝ) + n + 1 := by positivity
      have key : (1 : ℝ) / ((n : ℝ) + Q + 1) ^ 2 ≤ 1 / ((Q : ℝ) + n) - 1 / ((Q : ℝ) + n + 1) := by
        rw [div_sub_div _ _ (ne_of_gt h1) (ne_of_gt h2),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h1.le, h2.le]
      have hsplit : ∑ i ∈ range (n + 1), (1 : ℝ) / ((i : ℝ) + Q + 1) ^ 2
          = (∑ i ∈ range n, (1 : ℝ) / ((i : ℝ) + Q + 1) ^ 2) + 1 / ((n : ℝ) + Q + 1) ^ 2 :=
        Finset.sum_range_succ _ _
      have hcast : ((Q : ℝ) + ((n + 1 : ℕ) : ℝ)) = (Q : ℝ) + n + 1 := by push_cast; ring
      rw [hsplit, hcast]
      linarith

/-- The tail of `∑ 1/q²` beyond `Q` is at most `1/Q`. -/
lemma tsum_inv_sq_tail_le (Q : ℕ) (hQ : 1 ≤ Q) :
    ∑' i : ℕ, (1 : ℝ) / ((i : ℝ) + Q + 1) ^ 2 ≤ 1 / (Q : ℝ) := by
  refine Real.tsum_le_of_sum_range_le (fun i => by positivity) (fun n => ?_)
  have h := sum_range_inv_sq_shift_le Q hQ n
  have hpos : (0 : ℝ) ≤ 1 / ((Q : ℝ) + n) := by positivity
  linarith

/-- The comparison series `∑ C/q²` is summable (the `q = 0` term being `0`). -/
lemma summable_const_div_nat_sq (C : ℝ) : Summable (fun q : ℕ => C / (q : ℝ) ^ 2) := by
  have h : Summable (fun q : ℕ => (1 : ℝ) / (q : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow).2 (by norm_num)
  simpa [div_eq_mul_inv, mul_comm] using h.mul_left C

/--
**Singular Series Convergence Rate.**

Let `a : ℕ → ℝ` be the terms of a singular series, i.e. an arithmetic series whose
`q`-th term obeys the standard effective bound `|a q| ≤ C / q²` for `q ≥ 1` (with `a 0 = 0`).
Then the series converges, and truncating it at level `Q ≥ 1` incurs an error of at most
`C / Q` — an effective convergence rate for the singular series.
-/
theorem SingularSeriesConvergenceRate (a : ℕ → ℝ) (C : ℝ)
    (ha0 : a 0 = 0) (ha : ∀ q : ℕ, 1 ≤ q → |a q| ≤ C / (q : ℝ) ^ 2) :
    Summable a ∧
      ∀ Q : ℕ, 1 ≤ Q → |(∑' q : ℕ, a q) - ∑ q ∈ Finset.Icc 1 Q, a q| ≤ C / (Q : ℝ) := by
  have hC : 0 ≤ C := by
    have h := ha 1 le_rfl
    have : (0 : ℝ) ≤ C / (1 : ℝ) ^ 2 := le_trans (abs_nonneg _) (by simpa using h)
    simpa using this
  set g : ℕ → ℝ := fun q => C / (q : ℝ) ^ 2 with hg
  have hgs : Summable g := summable_const_div_nat_sq C
  have hbound : ∀ q : ℕ, ‖a q‖ ≤ g q := by
    intro q
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp [ha0, hg]
    · simpa [hg, Real.norm_eq_abs] using ha q h
  have hsum : Summable a := hgs.of_norm_bounded hbound
  refine ⟨hsum, fun Q hQ => ?_⟩
  -- split off the first `Q+1` terms
  have hsplit := hsum.sum_add_tsum_nat_add (Q + 1)
  have hrange : ∑ i ∈ range (Q + 1), a i = ∑ q ∈ Finset.Icc 1 Q, a q := by
    have hins : range (Q + 1) = insert 0 (Finset.Icc 1 Q) := by
      ext x; simp; omega
    rw [hins, Finset.sum_insert (by simp), ha0, zero_add]
  have hkey : (∑' q : ℕ, a q) - ∑ q ∈ Finset.Icc 1 Q, a q = ∑' i : ℕ, a (i + (Q + 1)) := by
    rw [← hrange, ← hsplit]; ring
  rw [hkey]
  -- bound the tail
  have hgtail : Summable (fun i : ℕ => g (i + (Q + 1))) := (summable_nat_add_iff _).2 hgs
  have habs : Summable (fun i : ℕ => |a (i + (Q + 1))|) := by
    refine hgtail.of_nonneg_of_le (fun i => abs_nonneg _) (fun i => ?_)
    simpa [Real.norm_eq_abs] using hbound (i + (Q + 1))
  calc |∑' i : ℕ, a (i + (Q + 1))| ≤ ∑' i : ℕ, |a (i + (Q + 1))| := by
        simpa [Real.norm_eq_abs] using
          norm_tsum_le_tsum_norm (f := fun i : ℕ => a (i + (Q + 1)))
            (by simpa [Real.norm_eq_abs] using habs)
    _ ≤ ∑' i : ℕ, g (i + (Q + 1)) :=
        habs.tsum_le_tsum (fun i => by simpa [Real.norm_eq_abs] using hbound (i + (Q + 1))) hgtail
    _ = C * ∑' i : ℕ, (1 : ℝ) / ((i : ℝ) + Q + 1) ^ 2 := by
        rw [← tsum_mul_left]
        refine tsum_congr (fun i => ?_)
        have : ((i + (Q + 1) : ℕ) : ℝ) = (i : ℝ) + Q + 1 := by push_cast; ring
        rw [hg]
        simp [this, div_eq_mul_inv]
    _ ≤ C * (1 / (Q : ℝ)) := mul_le_mul_of_nonneg_left (tsum_inv_sq_tail_le Q hQ) hC
    _ = C / (Q : ℝ) := by ring

/--
**Concrete arithmetic instance.** A Möbius-weighted singular series
`𝔖(w) = ∑_{q ≥ 1} μ(q) · w q / q²` with bounded local factors `|w q| ≤ 1`
converges, and its truncation at level `Q ≥ 1` has error at most `1 / Q`.
-/
theorem moebius_singular_series_convergence_rate (w : ℕ → ℝ) (hw : ∀ q : ℕ, |w q| ≤ 1) :
    Summable (fun q : ℕ => ((ArithmeticFunction.moebius q : ℤ) : ℝ) * w q / (q : ℝ) ^ 2) ∧
      ∀ Q : ℕ, 1 ≤ Q →
        |(∑' q : ℕ, ((ArithmeticFunction.moebius q : ℤ) : ℝ) * w q / (q : ℝ) ^ 2)
            - ∑ q ∈ Finset.Icc 1 Q,
                ((ArithmeticFunction.moebius q : ℤ) : ℝ) * w q / (q : ℝ) ^ 2| ≤ 1 / (Q : ℝ) := by
  refine SingularSeriesConvergenceRate _ 1 (by simp) (fun q hq => ?_)
  have hmu : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
    rcases eq_or_ne (ArithmeticFunction.moebius q) 0 with h | h
    · simp [h]
    · rcases (ArithmeticFunction.moebius_ne_zero_iff_eq_or).1 h with h1 | h1 <;> simp [h1]
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (q : ℝ) ^ 2), abs_mul]
  gcongr
  exact mul_le_one₀ hmu (abs_nonneg _) (hw q)

/-- Sanity check / instance of the general bound: the hypotheses are satisfiable, e.g. for
`a q = 1/q²` (with the convention `a 0 = 0`), where truncation at `Q` costs at most `1/Q`. -/
example : ∀ Q : ℕ, 1 ≤ Q →
    |(∑' q : ℕ, (1 : ℝ) / (q : ℝ) ^ 2) - ∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) / (q : ℝ) ^ 2|
      ≤ 1 / (Q : ℝ) :=
  (SingularSeriesConvergenceRate (fun q => 1 / (q : ℝ) ^ 2) 1 (by norm_num)
    (fun q hq => by
      have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
      rw [abs_of_nonneg (by positivity)])).2

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

