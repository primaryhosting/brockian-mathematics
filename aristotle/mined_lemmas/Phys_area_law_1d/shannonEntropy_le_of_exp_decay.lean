import Mathlib
/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header block is required to be the first content of the file; Lean 4 requires
`import` statements to precede every other command, including module docstrings, so the
single `import Mathlib` line above is the only thing preceding it.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

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

namespace Phys

/-! ## Shannon entropy of a finite spectrum -/

/-- Shannon (von Neumann) entropy of a finite family of probabilities. -/

theorem shannonEntropy_le_of_exp_decay {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (rank : ι → ℕ) (hrank : Function.Injective rank)
    (hdecay : ∀ i, p i ≤ C * Real.exp (-(c * rank i))) :
    shannonEntropy p ≤ areaLawBound C c := by
  set t : ℝ := Real.exp (-c) with ht_def
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := by
    rw [ht_def, Real.exp_lt_one_iff]; linarith
  have hpow : ∀ n : ℕ, t ^ n = Real.exp (-(c * n)) := by
    intro n
    rw [ht_def, ← Real.exp_nat_mul]
    ring_nf
  have hdecay' : ∀ i, p i ≤ C * t ^ (rank i) := by
    intro i; rw [hpow]; exact hdecay i
  have hone_sub : (0 : ℝ) < 1 - t := by linarith
  -- the reference distribution
  set q : ι → ℝ := fun i => (1 - t) * t ^ (rank i) with hq_def
  have hqpos : ∀ i, 0 < q i := fun i => mul_pos hone_sub (pow_pos ht0 _)
  have hqsum : ∑ i, q i ≤ 1 := sum_geometric_rank_le_one ht0 ht1 rank hrank
  have hcross := shannonEntropy_le_cross p q hp hpsum hqpos hqsum
  have hlogq : ∀ i, -Real.log (q i) = -Real.log (1 - t) + c * (rank i : ℝ) := by
    intro i
    rw [hq_def]
    simp only
    rw [Real.log_mul hone_sub.ne' (pow_pos ht0 _).ne', Real.log_pow, ht_def, Real.log_exp]
    ring
  have hrewrite : ∑ i, p i * (-Real.log (q i))
      = -Real.log (1 - t) + c * ∑ i, p i * (rank i : ℝ) := by
    have : ∀ i ∈ (Finset.univ : Finset ι),
        p i * (-Real.log (q i))
          = (-Real.log (1 - t)) * p i + c * (p i * (rank i : ℝ)) := by
      intro i _
      rw [hlogq i]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hpsum, mul_one]
  have hmean : ∑ i, p i * (rank i : ℝ) ≤ C * (t / (1 - t) ^ 2) :=
    sum_rank_le p hC ht0 ht1 rank hrank hdecay'
  have : shannonEntropy p ≤ -Real.log (1 - t) + c * (C * (t / (1 - t) ^ 2)) := by
    rw [hrewrite] at hcross
    have := mul_le_mul_of_nonneg_left hmean hc.le
    linarith
  simpa [areaLawBound, ht_def] using this

/-! ## Bipartite pure states, reduced density matrices, entanglement entropy -/

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The reduced density matrix on the `A` factor of a bipartite pure state
`psi : A → B → ℂ` (given as its matrix of coefficients in a product basis). -/
