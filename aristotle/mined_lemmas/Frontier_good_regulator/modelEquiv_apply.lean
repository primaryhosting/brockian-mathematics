/-!
# Good Regulator
Category: Frontier Mind
Target: Frontier.good_regulator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/--
**Conant–Ashby "Good Regulator" theorem (deterministic base case).**

Setting: a system with state space `S`, a regulator with action space `R`, and an
outcome map `h : S → R → Z`.  The regulation goal is the single "good" outcome `z₀`
(the error-free, minimal-entropy case of the Conant–Ashby setup).

Hypothesis `hgood`: for every system state there is exactly one regulator action that
achieves the good outcome — i.e. regulation is possible and of minimal variety.

Conclusion: there is a map `m : S → R` such that

* `m` is a successful regulator;
* **every** good regulator equals `m`, so a good regulator is necessarily a *function of
  the system state*: it is a model of the system;
* `m s = m s'` holds exactly when `s` and `s'` impose the same requirement on the
  regulator.  Hence the regulator's actions are in bijection with the distinguishable
  states of the system: the regulator *contains a model* of the system.

The proof is elementary; the whole content is the uniqueness clause packaged in
`hgood` (this is exactly Mathlib's `ExistsUnique.unique`, spelled out here), so the file
needs no imports at all.
-/

theorem modelEquiv_apply (s : S) :
    (modelEquiv hgood (Quotient.mk (sysSetoid h z₀) s) : R) = regulatorModel h z₀ hgood s :=
  rfl

end Model

end Frontier

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

