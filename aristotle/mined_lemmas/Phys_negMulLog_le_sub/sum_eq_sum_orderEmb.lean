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

theorem sum_eq_sum_orderEmb {N : ℕ} (t : Finset (Fin N)) (p : Fin N → ℝ) :
    ∑ i ∈ t, p i = ∑ a : Fin t.card, p (t.orderEmbOfFin rfl a) := by
  have h : t = Finset.map (t.orderEmbOfFin rfl).toEmbedding Finset.univ := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and, RelEmbedding.coe_toEmbedding]
    constructor
    · intro hi
      have hr : i ∈ Set.range (t.orderEmbOfFin (rfl : t.card = t.card)) := by
        rw [Finset.range_orderEmbOfFin]; exact hi
      obtain ⟨a, ha⟩ := hr
      exact ⟨a, ha⟩
    · rintro ⟨a, rfl⟩; exact Finset.orderEmbOfFin_mem t rfl a
  conv_lhs => rw [h]
  rw [Finset.sum_map]
  rfl

/-- Sum over the first `j` indices, written as a sum over `Fin j`. -/
