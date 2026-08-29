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

theorem mean_eq_sum_tails {N : ℕ} (p : Fin N → ℝ) :
    ∑ i : Fin N, (i : ℝ) * p i
      = ∑ k ∈ Finset.Ico 1 N, ∑ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ (i : ℕ)), p i := by
  have h := weighted_layer_cake p (fun _ => (1 : ℝ))
  simpa using h

/-! ## Entropy bounds from decaying tails -/

/-- Exponentially decaying tails force a bounded mean index. -/
