/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: the requested header is reproduced verbatim above, but as an ordinary block comment
`/- ... -/` rather than a module docstring `/-! ... -/`, since Lean 4 does not allow a module
docstring to precede the `import` commands.)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- A finite set of nonnegative integers `H` (a *gap range*, or prime tuple pattern) is
*admissible* when, for every prime `p`, the reductions of the elements of `H` modulo `p`
do not cover all of `ZMod p`.  Equivalently the local factor
`1 - ν_H(p)/p` of the Hardy–Littlewood singular series is strictly positive at every prime,
which is exactly the condition for the singular series `𝔖(H)` to be nonzero. -/

theorem admissible_gapRange_0_20 :
    AdmissibleTuple ({0, 2, 6, 8, 12, 18, 20} : Finset ℕ) := by
  rw [← admissibleTuple_image_add_iff _ 11]
  have hset : (({0, 2, 6, 8, 12, 18, 20} : Finset ℕ).image (fun h => h + 11))
      = ({11, 13, 17, 19, 23, 29, 31} : Finset ℕ) := by decide
  rw [hset]
  exact admissible_primeBlock_11_31

end Brockian

