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

import Mathlib
import RequestProject.Savitch.Reach

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The deterministic simulator

This file defines the deterministic machine used in Savitch's theorem: an explicit
iterative (stack based) implementation of the recursive procedure

```
REACH d u v  =  if d = 0 then (u = v ∨ u → v)
                else ∃ m, REACH (d-1) u m ∧ REACH (d-1) m v
```

together with its encoding into bit strings and the space accounting: a well-formed
state occupies `O((f n)²)` bits, because the stack holds at most `f n + 2` frames of
`O(f n)` bits each.
-/

namespace CS
namespace Savitch

/-- Classical truth value of a proposition. -/

lemma encRegs_length_le (l : List Word) (c : ℕ) (h : ∀ w ∈ l, w.length ≤ c) :
    (encRegs l).length ≤ 2 * l.length * (c + 1) + 2 := by
  have hflat : (l.flatMap dbl).length ≤ 2 * l.length * (c + 1) := by
    induction l with
    | nil => simp
    | cons w l ih =>
      have hw : w.length ≤ c := h w (by simp)
      have ih' := ih (fun v hv => h v (by simp [hv]))
      simp only [List.flatMap_cons, List.length_append, dbl_length, List.length_cons]
      have : 2 * (l.length + 1) * (c + 1) = 2 * l.length * (c + 1) + 2 * (c + 1) := by ring
      omega
  have : (encRegs l).length = (l.flatMap dbl).length + 2 := by
    simp [encRegs]
  omega

end CS

import Mathlib
import RequestProject.Savitch.Machines

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Bounded reachability in configuration graphs

Fix a nondeterministic machine `N` and an input `x`.  We study reachability in the
configuration graph of `N` on `x`, restricted to configurations of length at most `s`.

* `stepsTo N x k u v` : `v` is reached from `u` in exactly `k` steps;
* `ReachIn N x k u v` : `v` is reached from `u` in at most `k` steps;
* `R N x s d u v`     : the *Savitch predicate*, the doubling recursion which unfolds
  to "`v` is reachable from `u` in at most `2 ^ d` steps".

The two main results are `reach_bounded` (reachability implies reachability within
`#configurations` steps) and `reach_iff_R` (reachability is exactly `R` at depth `s+1`).
-/

namespace CS
namespace Savitch

/-! ### The list of all configurations of bounded length -/

/-- All bit strings of a given length. -/
