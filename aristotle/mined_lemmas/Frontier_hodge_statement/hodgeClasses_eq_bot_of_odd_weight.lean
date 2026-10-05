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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open TensorProduct

/-! ## The linear-algebra set-up

For a smooth complex projective variety `X`, the singular cohomology group
`V = H^{2p}(X, ℚ)` is a finite-dimensional `ℚ`-vector space whose complexification
`ℂ ⊗[ℚ] V` carries the Hodge decomposition into subspaces `H^{r,s}` with `r + s = 2p`,
exchanged by complex conjugation.  A *Hodge class* is a rational class whose image in the
complexification lies in the `(p,p)`-part, and the Hodge conjecture asserts that every
Hodge class is a rational combination of classes of algebraic cycles of codimension `p`.

Below we axiomatise exactly this data: `HodgeStructure w` records the rational vector
space together with its Hodge decomposition of weight `w`, `CycleClasses S p` records the
subspace of classes of algebraic cycles (which is always contained in the space of Hodge
classes — this containment is a theorem of Hodge theory, taken here as part of the data),
and `HodgeConjectureFor` is the assertion that the two subspaces agree. -/

/-- Complex conjugation on the complexification `ℂ ⊗[ℚ] V`; it is `ℚ`-linear (and
`ℂ`-semilinear). -/

lemma hodgeClasses_eq_bot_of_odd_weight {w : ℤ} (S : HodgeStructure w) (hw : Odd w)
    (p : ℤ) : S.hodgeClasses p = ⊥ := by
  refine hodgeClasses_eq_bot_of_H_eq_bot S p (S.weight (p, p) ?_)
  intro hcon
  rcases hw with ⟨k, hk⟩
  omega

/-- Base case: whenever the space of Hodge classes vanishes, the conjecture holds. -/
