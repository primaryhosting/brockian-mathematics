/-
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## Complex conjugation on a complexified rational vector space -/

/-- Complex conjugation, viewed as a `ℚ`-linear endomorphism of `ℂ`. -/

lemma hodgeClasses_le_alg_of_gt_dim {d : ℕ} (X : HodgeVarietyData d) (p : ℕ) (hp : d < p) :
    hodgeClasses (X.hs p) (p : ℤ) ≤ X.alg p := by
  rw [hodgeClasses_eq_bot_of_trivial _ _ (X.vanishing p hp)]
  exact bot_le

/-- **Base case / Lean-checked reduction of the Hodge conjecture.**

For a smooth projective complex variety of dimension `d ≤ 2` (a point, a curve or a surface),
the Hodge conjecture follows from just three inputs:

* degree `0`: the fundamental class generates the Hodge classes of `H^0`;
* degree `2` (`p = 1`): the Lefschetz `(1,1)`-theorem, i.e. Hodge classes in `H^2` are classes
  of divisors;
* top degree `p = d`: the class of a point generates the Hodge classes of `H^{2d}`.

Indeed all remaining cohomological degrees are above the dimension, hence carry no cohomology.
-/
