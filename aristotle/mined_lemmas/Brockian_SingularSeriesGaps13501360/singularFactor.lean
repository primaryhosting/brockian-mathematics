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

noncomputable def singularFactor (p : ℕ) (H : Finset ℤ) : ℝ :=
  (1 - (nu p H : ℝ) / p) / (1 - 1 / (p : ℝ)) ^ H.card

/-- The partial Hardy–Littlewood singular series: the product of the local factors over all
primes below `N`. -/
