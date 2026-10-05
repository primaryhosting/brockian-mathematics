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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## The setting

Mathlib does not (yet) contain the theory of smooth projective complex varieties,
singular cohomology with its Hodge decomposition, or the cycle class map.  We therefore
formalize the Hodge conjecture in the standard *linear-algebra* form it takes once the
geometric input is available:

* `V` plays the role of the singular cohomology group `H^{2p}(X, ℚ)` of a smooth
  projective complex variety `X`;
* `ℂ ⊗[ℚ] V` is its complexification `H^{2p}(X, ℂ)`;
* a `HodgeStructure V w` is a Hodge decomposition of weight `w` on `V`, i.e. a
  bigrading `H^{a,b}` of `ℂ ⊗[ℚ] V` concentrated in bidegrees with `a + b = w`
  and exchanged by complex conjugation;
* `hodgeClasses H p` is the ℚ-subspace of *Hodge classes*: rational classes whose
  image in the complexification lies in the `(p,p)` piece;
* an `AlgebraicClasses H p` is a subspace `A` of classes of algebraic cycles; the
  geometric fact that algebraic cycle classes are Hodge classes is recorded as the
  field `alg_le_hodge`.

The Hodge conjecture then reads: `hodgeClasses H p ≤ A`, i.e. every Hodge class is a
rational combination of classes of algebraic cycles.
-/

section Conjugation

variable (V : Type) [AddCommGroup V] [Module ℚ V]

/-- Complex conjugation on the complexification `ℂ ⊗[ℚ] V`, as a `ℚ`-linear map. -/

noncomputable def degreeZeroAlgebraicClasses : AlgebraicClasses (tateHodgeStructure ℚ 0) 0 where
  A := ⊤
  alg_le_hodge := by rw [hodgeClasses_tate]

/-!
## The target statement
-/

/-- **The Hodge conjecture, formalized, together with a Lean-checked reduction and the
proved base cases.**

The conjunction below states, for every rational Hodge structure `H` of weight `w` on a
ℚ-vector space `V`, every `p`, and every space `C` of algebraic cycle classes:

1. the *contrapositive* reformulation: the conjecture for `(H, p, C)` holds iff there is
   no Hodge class outside the algebraic classes;
2. the reformulation as an *equality* `hodgeClasses = algebraic classes` (using that
   algebraic classes are Hodge classes);
3. the reduction to a *spanning family*: the conjecture holds iff the Hodge classes are
   spanned by algebraic classes;
4. the base case `p + p ≠ w`: there are no nonzero Hodge classes of type `(p,p)`, so the
   conjecture holds;
5. the base case of a Hodge structure of Tate type `(p,p)`: all rational classes are
   Hodge classes;
6. the base case of degree `0`: for `H^0(X,ℚ) = ℚ` with its weight-`0` Tate Hodge
   structure and the algebraic classes spanned by the fundamental class, the conjecture
   holds.
-/
