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

theorem entropy_le_of_reference {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (r : Fin N → ℝ) (hr : ∀ i, 0 < r i) (hrsum : ∑ i, r i ≤ 1) :
    ∑ i, Real.negMulLog (p i) ≤ ∑ i, p i * (-Real.log (r i)) := by
  have h : ∑ i, Real.negMulLog (p i)
      ≤ ∑ i : Fin N, ((r i - p i) + p i * (-Real.log (r i))) :=
    Finset.sum_le_sum (fun i _ => negMulLog_le_sub (p i) (r i) (hp i) (hr i))
  refine h.trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum]
  linarith

/-! ## Rearrangement facts -/

/-- A strictly monotone map between `Fin` types cannot decrease indices. -/
