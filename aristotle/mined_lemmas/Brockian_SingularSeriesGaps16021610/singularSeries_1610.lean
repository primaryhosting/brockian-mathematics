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

lemma singularSeries_1610 : singularSeries 1610 = 352 / 105 := by
  rw [singularSeries, if_pos (by decide), singularFactor, primeFactors_1610]
  norm_num [Finset.prod_insert, Finset.erase_insert_of_ne]

end Values

/-- **Admissible gaps and singular series values in the range `1602 ≤ d ≤ 1610`.**

* a gap `d` in this range is admissible (i.e. `{0, d}` is an admissible pair) precisely
  when `d` is even;
* every admissible gap in this range has positive singular series;
* the gap `d = 1608` strictly maximizes the singular series over the range, with value
  `264/65` (in units of the twin prime constant `C₂`). -/
