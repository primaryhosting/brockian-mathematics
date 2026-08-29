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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-! ## Complexification -/

/-- Complex conjugation acting on the complexification `ℂ ⊗[ℚ] V` of a `ℚ`-vector space `V`,
as a `ℚ`-linear automorphism. -/

theorem hodgeConjecture_pointDatum : HodgeConjecture pointDatum := le_top

/-! ## The statement -/

/--
**Hodge statement.**

The Hodge conjecture, as formalized above, together with a Lean-checked reduction and the
verified base cases:

1. *(Formulation.)* For every Hodge datum `X` — a pure rational Hodge structure of weight
   `2p` on `H^{2p}(X, ℚ)` together with the subspace `alg` of classes of algebraic cycles of
   codimension `p`, which is contained in the space of Hodge classes — the Hodge conjecture
   for `X` is exactly the assertion that the space of Hodge classes equals the space of
   algebraic classes.
2. *(Non-vacuity / base case.)* There exists such a datum, namely that of a point, and the
   conjecture holds for it.
3. *(Reduction to generators.)* The conjecture for `X` follows from the algebraicity of any
   spanning set of the space of Hodge classes.
4. *(Invariance.)* The conjecture is invariant under isomorphisms of Hodge data.
5. *(Base case: vanishing `(p,p)`-part.)* If `H^{p,p} = 0` then the conjecture holds for `X`.
6. *(Base case: rank ≤ 1.)* If `H^{2p}(X, ℚ)` is at most one-dimensional and carries a
   nonzero algebraic class, then the conjecture holds for `X`.
-/
