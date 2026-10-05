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

theorem entropy_le_of_harmonic_tail_decay {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) {C : ℝ} (hC : 0 ≤ C)
    (htail : ∀ k : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ (i : ℕ)), p i
      ≤ C / ((k : ℝ) + 1)) :
    ∑ i, Real.negMulLog (p i) ≤ Real.log 2 + 2 * C := by
  set r : Fin N → ℝ := fun i => (1 / 2) * (1 / (((i : ℕ) : ℝ) + 1) ^ 2) with hrdef
  have hr : ∀ i, 0 < r i := fun i => by rw [hrdef]; positivity
  have hrsum : ∑ i, r i ≤ 1 := by
    rw [hrdef, ← Finset.mul_sum]
    have h : ∑ i : Fin N, (1 / (((i : ℕ) : ℝ) + 1) ^ 2)
        = ∑ i ∈ Finset.range N, (1 / ((i : ℝ) + 1) ^ 2) :=
      Fin.sum_univ_eq_sum_range (fun i => 1 / ((i : ℝ) + 1) ^ 2) N
    rw [h]
    have h2 := sum_inv_sq_le N
    have h3 : (1 : ℝ) ≤ ((max N 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right N 1
    have h4 : 0 < 1 / ((max N 1 : ℕ) : ℝ) := by positivity
    linarith
  refine (entropy_le_of_reference p hp hsum r hr hrsum).trans ?_
  have hlogr : ∀ i : Fin N,
      -Real.log (r i) = Real.log 2 + 2 * Real.log (((i : ℕ) : ℝ) + 1) := by
    intro i
    rw [hrdef]
    simp only
    rw [Real.log_mul (by norm_num) (by positivity)]
    rw [Real.log_div one_ne_zero (by positivity), Real.log_div one_ne_zero (by positivity)]
    rw [Real.log_pow]
    simp
    ring
  have hsplit : ∑ i : Fin N, p i * (-Real.log (r i))
      = (∑ i : Fin N, p i) * Real.log 2
        + 2 * ∑ i : Fin N, p i * Real.log (((i : ℕ) : ℝ) + 1) := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [hlogr i]; ring)
  rw [hsplit, hsum, one_mul]
  have := log_mean_le_of_harmonic_tail_decay p hp hC htail
  linarith

/-! ## Bipartite entanglement entropy -/

section Bipartite

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]

/-- The **Schmidt spectrum** of a bipartite pure state `psi : Matrix A B ℂ` (the state
`∑ a b, psi a b • |a⟩ ⊗ |b⟩`): the eigenvalues of the reduced density matrix `psi * psiᴴ` on
the left factor, i.e. the squared Schmidt coefficients. -/
