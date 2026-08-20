import Mathlib
/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to be the very first commands of a
file, so the module docstring above is placed immediately after `import Mathlib`.

## Contents

* `Frontier.ContainsAP A k` : the set `A ⊆ ℕ` contains an arithmetic progression of length `k`
  with positive common difference.
* `Frontier.upperDensity A` : the upper asymptotic density of `A ⊆ ℕ`.
* `Frontier.FinitarySzemeredi k` : the finitary form of Szemerédi's theorem for progressions of
  length `k`.
* `Frontier.furstenberg_szemeredi` : the reduction of Szemerédi's theorem (positive upper density
  sets of naturals contain arbitrarily long arithmetic progressions) to its finitary form.
* `Frontier.finitarySzemeredi_three` : the finitary statement for `k = 3`, deduced from Roth's
  theorem (available in Mathlib as `roth_3ap_theorem_nat`).
* `Frontier.furstenberg_szemeredi_three` : the resulting *unconditional* base case: every set of
  naturals of positive upper density contains a 3-term arithmetic progression.
-/

open Filter Finset

open scoped Classical

namespace Frontier

/-- `ContainsAP A k` says that `A` contains an arithmetic progression of length `k` with
positive common difference. -/

lemma containsAP_three_of_not_threeAPFree {s : Set ℕ} (h : ¬ ThreeAPFree s) :
    ContainsAP s 3 := by
  rw [ThreeAPFree] at h
  push_neg at h
  obtain ⟨a, ha, b, hb, c, hc, habc, hab⟩ := h
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · refine ⟨a, b - a, by omega, ?_⟩
    intro i hi
    interval_cases i
    · simpa using ha
    · have h1 : a + 1 * (b - a) = b := by omega
      rw [h1]; exact hb
    · have h2 : a + 2 * (b - a) = c := by omega
      rw [h2]; exact hc
  · refine ⟨c, b - c, by omega, ?_⟩
    intro i hi
    interval_cases i
    · simpa using hc
    · have h1 : c + 1 * (b - c) = b := by omega
      rw [h1]; exact hb
    · have h2 : c + 2 * (b - c) = a := by omega
      rw [h2]; exact ha

/-- The finitary Szemerédi statement for `k = 3`, i.e. **Roth's theorem**. -/
