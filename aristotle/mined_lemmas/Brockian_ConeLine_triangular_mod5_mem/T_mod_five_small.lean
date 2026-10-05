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

/-!
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Brockian
namespace ConeLine

/-- The `n`-th triangular number, computed in `ℕ` (so the division is exact). -/

lemma T_mod_five_small : ∀ m < 10, T m % 5 = 0 ∨ T m % 5 = 1 ∨ T m % 5 = 3 := by decide

/-- Triangular numbers land only on the rays `0, 1, 3` modulo `5`:
for every `n`, `T n = n (n + 1) / 2` satisfies `T n mod 5 ∈ {0, 1, 3}`,
so the rays `2` and `4` carry no triangular number. -/
