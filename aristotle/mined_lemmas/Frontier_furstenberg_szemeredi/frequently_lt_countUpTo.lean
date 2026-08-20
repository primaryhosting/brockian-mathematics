/-
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

open scoped Classical in
/-- The number of elements of `A` below `n`. -/

lemma frequently_lt_countUpTo {A : Set ℕ} {c : ℝ} (hc : c < upperDensity A) :
    ∃ᶠ n : ℕ in atTop, c * n < (countUpTo A n : ℝ) := by
  have h := Filter.frequently_lt_of_lt_limsup (isCoboundedUnder_density A) hc
  have h1 : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact_mod_cast hn
  refine (h.and_eventually h1).mono ?_
  rintro n ⟨hlt, hn⟩
  exact (lt_div_iff₀ hn).1 hlt

/-- **Reduction**: the finitary form of Szemerédi's theorem implies the infinitary,
density form: every set of naturals of positive upper density contains arithmetic
progressions of every finite length.

This is the statement obtained from Furstenberg's multiple recurrence theorem via the
Furstenberg correspondence principle; here it is derived, in a Lean-checked way, from the
finitary statement `SzemerediFinitary` taken as a hypothesis. Unconditionally we also prove:
the case `k = 3` (`Frontier.hasAP_three_of_pos_upperDensity`, from Roth's theorem), the
finitary property for `k = 3` (`Frontier.szemerediFinitary_three`), and the case of all `k`
for density above `1 - 1/(2k)` (`Frontier.hasAP_of_upperDensity_gt`). -/
