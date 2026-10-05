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

lemma nu_two_pair_of_odd {d : ℤ} (hd : ¬ Even d) : nu 2 ({0, d} : Finset ℤ) = 2 := by
  refine nu_pair_of_not_dvd 2 ?_
  rintro ⟨k, rfl⟩
  exact hd ⟨k, by ring⟩

/-- A pair `{0, d}` with `d ≠ 0` is admissible exactly when `d` is even. -/
