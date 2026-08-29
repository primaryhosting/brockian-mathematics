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

noncomputable def sstep (N : NDetMachine) (f : ℕ → ℕ) : SavState → Option Bool → SavState
  | .count k, none => .scan k 0
  | .count k, some _ => .count (k + 1)
  | .scan n j, _ =>
      if j < (cands (f n)).length then
        (if toBool (N.accept ((cands (f n)).getD j [])) then
          .main n j [⟨f n + 1, N.init, (cands (f n)).getD j [], 0, 0⟩] false
        else .scan n (j + 1))
      else .done false
  | .main n j [] ret, _ => if ret then .done true else .scan n (j + 1)
  | .main n j (F :: rest) ret, b =>
      if F.phase = 0 then
        (if F.level = 0 then .main n j rest (toBool (F.u = F.v ∨ N.step F.u b F.v))
        else .main n j (⟨F.level - 1, F.u, (cands (f n)).getD 0 [], 0, 0⟩ ::
          ⟨F.level, F.u, F.v, 1, 0⟩ :: rest) ret)
      else if F.phase = 1 then
        (if ret then .main n j (⟨F.level - 1, (cands (f n)).getD F.idx [], F.v, 0, 0⟩ ::
            ⟨F.level, F.u, F.v, 2, F.idx⟩ :: rest) ret
        else advance n j F rest ret (f n))
      else
        (if ret then .main n j rest true else advance n j F rest ret (f n))
  | .done b, _ => .done b

/-- Halting states. -/
