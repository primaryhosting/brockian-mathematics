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

/-!
## Overview

Mathlib does not (yet) contain the theory of smooth projective complex varieties, their singular
cohomology, the Hodge decomposition, or cycle class maps.  We therefore develop, from scratch, the
linear-algebraic and axiomatic framework needed to *state* the Hodge conjecture, and we prove the
degree-`0` base case together with several Lean-checked reductions.

The framework consists of:

* `Frontier.Cx V`, the complexification `ℂ ⊗[ℚ] V` of a rational vector space, with its
  inclusion `Frontier.cxIncl` (proved injective) and its complex conjugation `Frontier.cxConj`;
* `Frontier.HodgeStr`, a pure rational Hodge structure: a finite-dimensional `ℚ`-vector space `V`
  of weight `w` together with a decomposition `V ⊗ ℂ = ⨁_{p+q=w} V^{p,q}` satisfying Hodge
  symmetry `conj (V^{p,q}) = V^{q,p}`;
* `Frontier.hodgeClasses H p`, the `ℚ`-subspace of rational classes of type `(p,p)`;
* `Frontier.HodgeTheory`, an axiomatization of the geometric input of the conjecture: a class of
  (smooth projective, connected) varieties, the Hodge structures on their rational cohomology, and
  the subspaces of classes of algebraic cycles;
* `Frontier.HodgeTheory.HodgeConjecture`, the statement of the Hodge conjecture for such data:
  every rational Hodge class of type `(p,p)` is a rational combination of classes of algebraic
  cycles.

The main theorem `Frontier.hodge_statement` proves the base case `p = 0` of the conjecture for
*every* Hodge theory: in cohomological degree `0` all Hodge classes are algebraic.
-/

namespace Frontier

/-! ## Complexification of a rational vector space -/

/-- The complexification `ℂ ⊗[ℚ] V` of a `ℚ`-vector space `V`. -/
abbrev Cx (V : Type) [AddCommGroup V] [Module ℚ V] : Type := ℂ ⊗[ℚ] V

/-- The canonical inclusion `V → V ⊗ ℂ`, `v ↦ 1 ⊗ v`. -/

theorem hodgeClasses_eq_top_of_weight_zero (H : HodgeStr) (hw : H.w = 0) (he : H.Effective) :
    hodgeClasses H 0 = ⊤ := by
  rw [hodgeClasses, H.Hpq_zero_eq_top hw he]
  simp

/-- If a Hodge structure has no `(p,p)`-classes at all, then it has no nonzero rational Hodge
classes of type `(p,p)`. -/
