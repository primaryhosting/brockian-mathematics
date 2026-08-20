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

lemma sum_geometric_rank_le_one {ι : Type*} [Fintype ι] {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (rank : ι → ℕ) (hrank : Function.Injective rank) :
    ∑ i, (1 - t) * t ^ (rank i) ≤ 1 := by
  have hsummable : Summable (fun n : ℕ => t ^ n) :=
    summable_geometric_of_lt_one ht0.le ht1
  have h1 : ∑ i, t ^ (rank i) = ∑ n ∈ Finset.image rank Finset.univ, t ^ n := by
    rw [Finset.sum_image (fun a _ b _ h => hrank h)]
  have h2 : ∑ n ∈ Finset.image rank Finset.univ, t ^ n ≤ ∑' n : ℕ, t ^ n :=
    hsummable.sum_le_tsum _ (fun n _ => pow_nonneg ht0.le n)
  have h3 : ∑' n : ℕ, t ^ n = (1 - t)⁻¹ := tsum_geometric_of_lt_one ht0.le ht1
  have ht : (0 : ℝ) < 1 - t := by linarith
  calc ∑ i, (1 - t) * t ^ (rank i) = (1 - t) * ∑ i, t ^ (rank i) := by
        rw [Finset.mul_sum]
    _ ≤ (1 - t) * (1 - t)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ ht.le
        rw [h1, ← h3]; exact h2
    _ = 1 := by field_simp

/-- Gibbs' inequality: the entropy of `p` is bounded by the cross entropy with any
subnormalized positive family `q`. -/
