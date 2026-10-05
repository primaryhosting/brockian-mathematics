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

theorem weighted_layer_cake {N : ℕ} (p : Fin N → ℝ) (w : ℕ → ℝ) :
    ∑ i : Fin N, (∑ k ∈ Finset.Ico 1 ((i : ℕ) + 1), w k) * p i
      = ∑ k ∈ Finset.Ico 1 N, w k
          * ∑ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ (i : ℕ)), p i := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm' (s' := fun i : Fin N => Finset.Ico 1 ((i : ℕ) + 1))
      (t' := (Finset.univ : Finset (Fin N)))]
  intro k i
  have hi := i.isLt
  simp only [Finset.mem_Ico, Finset.mem_univ, Finset.mem_filter, true_and, and_true]
  omega

/-- Layer-cake identity: the mean index equals the sum of the tail masses. -/
