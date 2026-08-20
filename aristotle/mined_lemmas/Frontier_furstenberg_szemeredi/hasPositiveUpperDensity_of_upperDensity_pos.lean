/- (Lean requires `import` to precede any module docstring, so the header below is a
plain block comment; it is repeated verbatim as a module docstring after the import.)
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset

namespace Frontier

noncomputable section

open Classical in
/-- The number of elements of `A` below `N`. -/

theorem hasPositiveUpperDensity_of_upperDensity_pos {A : Set ℕ}
    (h : 0 < upperDensity A) : HasPositiveUpperDensity A := by
  set f : ℕ → ℝ := fun N => (countBelow A N : ℝ) / N with hf
  have hnonneg : ∀ n, 0 ≤ f n := fun n => by positivity
  have hcb : IsCoboundedUnder (· ≤ ·) atTop f := isCoboundedUnder_le_of_le atTop hnonneg
  have hlim : limsup f atTop = upperDensity A := rfl
  refine ⟨upperDensity A / 2, by linarith, fun M => ?_⟩
  have hfreq : ∃ᶠ N in atTop, upperDensity A / 2 < f N :=
    frequently_lt_of_lt_limsup hcb (by rw [hlim]; linarith)
  obtain ⟨N, hlt, hge⟩ := (hfreq.and_eventually (eventually_ge_atTop (max M 1))).exists
  have hN1 : 1 ≤ N := le_trans (le_max_right M 1) hge
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
  refine ⟨N, le_trans (le_max_left M 1) hge, ?_⟩
  rw [hf] at hlt
  simp only at hlt
  rw [lt_div_iff₀ hNpos] at hlt
  linarith

/-- **Reduction (Lean-checked).**  The infinitary Szemerédi theorem for progressions of
length `k` -- every set of positive upper density contains a `k`-term arithmetic
progression -- follows from the finitary statement for `k`. -/
