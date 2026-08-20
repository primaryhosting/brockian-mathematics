import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- A finite set `H` of integers is *admissible* if for every prime `p` it fails to cover
all residue classes modulo `p`, i.e. some residue class mod `p` is missed by `H`.
This is the classical admissibility condition of the Hardy–Littlewood prime `k`-tuple
conjecture. -/

theorem SingularSeriesGaps16021610 :
    (∀ d : ℕ, 1602 ≤ d → d ≤ 1610 → (Admissible {0, (d : ℤ)} ↔ Even d)) ∧
    (∀ d : ℕ, 1602 ≤ d → d ≤ 1610 → Even d → 0 < singularSeries d) ∧
    (∀ d : ℕ, 1602 ≤ d → d ≤ 1610 → Even d → d ≠ 1608 →
      singularSeries d < singularSeries 1608) ∧
    singularSeries 1608 = 264 / 65 := by
  refine ⟨fun d _ _ => admissible_pair_iff_even d, ?_, ?_, singularSeries_1608⟩
  · intro d _ _ he
    exact singularSeries_pos_of_even he
  · intro d h1 h2 he hne
    interval_cases d <;>
      first
        | (exfalso; revert he; decide)
        | (exact absurd rfl hne)
        | norm_num [singularSeries_1602, singularSeries_1604, singularSeries_1606,
            singularSeries_1608, singularSeries_1610]

end Brockian

