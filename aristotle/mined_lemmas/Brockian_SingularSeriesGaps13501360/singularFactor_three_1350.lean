/-
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- The number of distinct residue classes modulo `p` occupied by the tuple `H`.
This is the local density `ν_p(H)` appearing in the Hardy–Littlewood singular series. -/

theorem singularFactor_three_1350 : singularFactor 3 ({0, 1350} : Finset ℤ) = 3 / 2 := by
  rw [singularFactor_pair_of_dvd (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- Concrete instance: `7 ∤ 1350`, so the local factor at `7` of the gap `1350` is `35/36`. -/
