/-
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Phys

/-! ## Complexified Minkowski space and the complex Lorentz group -/

/-- Complexified Minkowski space `ℂ⁴`. -/
abbrev CVec : Type := Fin 4 → ℂ

/-- The (bilinear, not sesquilinear) Minkowski form of signature `(+,-,-,-)` on complexified
Minkowski space. -/

lemma cptMap_involutive : Function.Involutive cptMap := fun x => by
  simp [cptMap]

/-- **CPT theorem (statement level).**  Every Lorentz-invariant local quantum field theory is
CPT invariant: its Wightman functions are unchanged when all spacetime arguments are
reflected, `x ↦ -x`.  The proof runs through the fact that the total reflection `-1` lies in
the identity component of the complex Lorentz group, so that CPT invariance is a consequence
of Lorentz invariance of the analytically continued Wightman functions.  (The locality
axiom of `QFT` is what makes that analytic continuation, and hence the hypothesis
`lorentz_invariant`, available; it is not used again in this final step.) -/
