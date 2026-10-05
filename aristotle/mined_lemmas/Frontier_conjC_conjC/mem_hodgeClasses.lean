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

theorem mem_hodgeClasses {w : ℤ} (H : HodgeStructure V w) (p : ℤ) (v : V) :
    v ∈ hodgeClasses H p ↔ (1 : ℂ) ⊗ₜ[ℚ] v ∈ H.F p p := Iff.rfl

/-- A space of algebraic cycle classes inside `V`, subject to the geometric fact that
classes of algebraic cycles are Hodge classes. -/
structure AlgebraicClasses {w : ℤ} (H : HodgeStructure V w) (p : ℤ) where
  /-- The ℚ-span of the classes of algebraic cycles of codimension `p`. -/
  A : Submodule ℚ V
  /-- Algebraic cycle classes are Hodge classes. -/
  alg_le_hodge : A ≤ hodgeClasses H p

/-- **The Hodge conjecture** for the datum `(H, p, C)`: every Hodge class of type `(p,p)`
is a rational linear combination of classes of algebraic cycles. -/
