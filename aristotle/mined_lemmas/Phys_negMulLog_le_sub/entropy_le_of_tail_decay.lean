import Mathlib
/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` to be the very first command of a module, so the
requested header block appears immediately after the single `import Mathlib` line.
-/

open scoped BigOperators ComplexOrder
open Matrix

namespace Phys

/-! ## Elementary entropy inequalities -/

/-- Gibbs-type pointwise bound: for `x ≥ 0` and a reference weight `r > 0`,
`-x log x ≤ (r - x) - x log r`. -/

theorem entropy_le_of_tail_decay {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) {C q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 0 ≤ C)
    (htail : ∀ k : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ (i : ℕ)), p i ≤ C * q ^ k) :
    ∑ i, Real.negMulLog (p i) ≤ (C * q / (1 - q)) * Real.log (1 / q) + Real.log (1 / (1 - q)) := by
  have hq1' : 0 < 1 - q := by linarith
  set r : Fin N → ℝ := fun i => (1 - q) * q ^ (i : ℕ) with hrdef
  have hr : ∀ i, 0 < r i := fun i => by rw [hrdef]; positivity
  have hrsum : ∑ i, r i ≤ 1 := by
    rw [hrdef, ← Finset.mul_sum]
    have h3 : ∑ i : Fin N, q ^ (i : ℕ) = ∑ i ∈ Finset.range N, q ^ i :=
      Fin.sum_univ_eq_sum_range (fun i => q ^ i) N
    rw [h3, geom_sum_eq (by linarith)]
    have hne : q - 1 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
    have h4 : (1 - q) * ((q ^ N - 1) / (q - 1)) = 1 - q ^ N := by
      field_simp
      linarith [sq_nonneg q]
    rw [h4]
    nlinarith [pow_nonneg hq0.le N]
  refine (entropy_le_of_reference p hp hsum r hr hrsum).trans ?_
  have hlogr : ∀ i : Fin N,
      -Real.log (r i) = (i : ℕ) * Real.log (1 / q) + Real.log (1 / (1 - q)) := by
    intro i
    rw [hrdef]
    simp only
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    rw [Real.log_div one_ne_zero (by positivity), Real.log_div one_ne_zero (by positivity)]
    simp
  have hsplit : ∑ i : Fin N, p i * (-Real.log (r i))
      = (∑ i : Fin N, (i : ℝ) * p i) * Real.log (1 / q)
        + (∑ i : Fin N, p i) * Real.log (1 / (1 - q)) := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [hlogr i]; ring)
  rw [hsplit, hsum, one_mul]
  have hlogq : 0 ≤ Real.log (1 / q) := Real.log_nonneg (by rw [le_div_iff₀ hq0]; linarith)
  have hmean := mean_le_of_tail_decay p hq0 hq1 hC htail
  nlinarith [hmean]

/-- `log (i+1)` is bounded by the `i`-th harmonic number. -/
