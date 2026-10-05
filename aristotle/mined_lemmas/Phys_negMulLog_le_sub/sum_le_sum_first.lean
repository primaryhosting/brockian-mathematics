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

theorem sum_le_sum_first {N : ℕ} {p : Fin N → ℝ} (hanti : Antitone p) (hp : ∀ i, 0 ≤ p i)
    (t : Finset (Fin N)) (k : ℕ) (hcard : t.card ≤ k) :
    ∑ i ∈ t, p i ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k), p i := by
  have hjN : t.card ≤ N := by simpa using Finset.card_le_univ t
  rw [sum_eq_sum_orderEmb t p]
  have step1 : ∑ a : Fin t.card, p (t.orderEmbOfFin rfl a)
      ≤ ∑ a : Fin t.card, p (Fin.castLE hjN a) := by
    refine Finset.sum_le_sum (fun a _ => hanti ?_)
    exact (Fin.le_def).2 (fin_le_of_strictMono (t.orderEmbOfFin rfl).strictMono a)
  refine step1.trans ?_
  rw [sum_castLE_eq hjN p]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hp i)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
  omega

/-! ## Layer-cake identities -/

/-- Weighted layer-cake identity: a weighted mean is the weighted sum of the tail masses. -/
