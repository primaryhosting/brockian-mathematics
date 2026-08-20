/-
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- The gap pattern `(0, 1602, 1610)`, i.e. the triple of integer shifts
`{0, 1602, 1610}` (gaps `1602` and `1610` from the base point). -/

theorem localFactor_pos_of_prime (p : ℕ) (hp : p.Prime) :
    0 < 1 - (nuP p : ℝ) / (p : ℝ) := by
  have hlt := nuP_lt_of_prime p hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have : (nuP p : ℝ) / (p : ℝ) < 1 := by
    rw [div_lt_one hp0]
    exact_mod_cast hlt
  linarith

end Brockian

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

