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

theorem sum_castLE_eq {N j : ℕ} (h : j ≤ N) (p : Fin N → ℝ) :
    ∑ a : Fin j, p (Fin.castLE h a)
      = ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), p i := by
  have hset : (Finset.univ.filter (fun i : Fin N => (i : ℕ) < j))
      = Finset.map ⟨Fin.castLE h, Fin.castLE_injective h⟩ (Finset.univ : Finset (Fin j)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro hi; exact ⟨⟨i, hi⟩, by simp⟩
    · rintro ⟨a, rfl⟩; simp
  rw [hset, Finset.sum_map]
  rfl

/-- For a nonincreasing nonnegative vector, no set of at most `k` indices carries more
weight than the first `k` indices. -/
