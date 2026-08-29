/-
# Ne Zero Re Gt One
Category: Riemann Program
Target: Riemann.zeta.ne_zero_re_gt_one
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Riemann
namespace zeta

/-- For every complex number `s` with `1 < s.re`, the Riemann zeta function does not
vanish at `s`.  Equivalently (contrapositive): every zero of `riemannZeta` lies in the
half-plane `s.re ≤ 1`. -/

theorem re_le_one_of_zeta_eq_zero (s : ℂ) (hs : riemannZeta s = 0) : s.re ≤ 1 := by
  by_contra h
  exact ne_zero_re_gt_one s (lt_of_not_ge h) hs

end zeta
end Riemann

