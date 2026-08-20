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

lemma sum_rank_le {ι : Type*} [Fintype ι] (p : ι → ℝ) {C t : ℝ} (hC : 0 ≤ C)
    (ht0 : 0 < t) (ht1 : t < 1)
    (rank : ι → ℕ) (hrank : Function.Injective rank)
    (hdecay : ∀ i, p i ≤ C * t ^ (rank i)) :
    ∑ i, p i * (rank i : ℝ) ≤ C * (t / (1 - t) ^ 2) := by
  have hsummable : Summable (fun n : ℕ => (n : ℝ) * t ^ n) := by
    have : ‖t‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos ht0]; exact ht1
    simpa using (summable_pow_mul_geometric_of_norm_lt_one 1 this)
  have hstep : ∑ i, p i * (rank i : ℝ) ≤ ∑ i, C * ((rank i : ℝ) * t ^ (rank i)) := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    have := hdecay i
    have hnn : (0 : ℝ) ≤ (rank i : ℝ) := Nat.cast_nonneg _
    nlinarith [pow_pos ht0 (rank i)]
  have h1 : ∑ i, ((rank i : ℝ) * t ^ (rank i))
      = ∑ n ∈ Finset.image rank Finset.univ, (n : ℝ) * t ^ n := by
    rw [Finset.sum_image (fun a _ b _ h => hrank h)]
  have h2 : ∑ n ∈ Finset.image rank Finset.univ, (n : ℝ) * t ^ n
      ≤ ∑' n : ℕ, (n : ℝ) * t ^ n :=
    hsummable.sum_le_tsum _
      (fun n _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht0.le n))
  have h3 : ∑' n : ℕ, (n : ℝ) * t ^ n = t / (1 - t) ^ 2 := by
    have : ‖t‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos ht0]; exact ht1
    exact tsum_coe_mul_geometric_of_norm_lt_one this
  calc ∑ i, p i * (rank i : ℝ) ≤ ∑ i, C * ((rank i : ℝ) * t ^ (rank i)) := hstep
    _ = C * ∑ i, ((rank i : ℝ) * t ^ (rank i)) := by rw [Finset.mul_sum]
    _ ≤ C * (t / (1 - t) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hC
        rw [h1, ← h3]; exact h2

/-- **Entropy bound from an exponentially decaying spectrum.**
If a probability vector `p` admits an injective ranking along which it decays
exponentially, `p i ≤ C * exp (-(c * rank i))`, then its Shannon entropy is bounded by
a constant depending only on `C` and `c`. -/
