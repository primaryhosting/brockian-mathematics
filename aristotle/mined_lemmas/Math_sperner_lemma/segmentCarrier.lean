/-
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
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

namespace Math

variable {V : Type*} [DecidableEq V]

/-- The `k`-dimensional faces (as `Finset`s of `k` vertices) occurring in the cells of `K`. -/

def segmentCarrier : ℕ → Finset ℕ := fun v => if v = 0 then {0} else if v = 1 then {0, 1} else {1}

/-- Non-vacuity check in a genuinely subdivided case: the segment `{0,1}` cut into the two
cells `{0,1}` and `{1,2}` is a triangulation in the sense of `Math.IsTriangulation`. -/
