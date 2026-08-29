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

import RequestProject.Blum.Cost

/-!
# The Blum speedup construction

We build, by the recursion theorem, a code `blumCode` computing a two-parameter family of
functions `f i t` (`i` an index bound, `t` a patch threshold) with the following features.

At stage `x`, the function `f i 0` diagonalises against every program `j ≥ i` which is
*cheap at stage `x`*, meaning that `cost j x ≤ M j x + x` where `M j x` is the maximal cost of
the programs `curry blumCode ⟨j+1, t⟩` (`t ≤ x`) on input `x`.  Each program is diagonalised
against at the first stage at which it becomes cheap, so `f i 0` and `f 0 0` differ at only
finitely many arguments; the parameter `t` lets one patch those finitely many arguments,
so that `f (j+1) t = f 0 0` for a suitable `t`.
-/

set_option maxHeartbeats 1000000

namespace CS

open Nat.Partrec Nat.Partrec.Code Primrec

/-! ### Generic form of the construction, parameterised by a cost function -/

/-- Maximal cost, according to `cf`, of the auxiliary programs with parameters `(j+1, t)`,
`t ≤ y`, on input `y`. -/

theorem evaln_getD_eq {c : Code} {n k v : ℕ} (h : eval c n = Part.some v)
    (hk : (evaln k c n).isSome) : (evaln k c n).getD 0 = v := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hk
  have hmem : x ∈ eval c n := evaln_sound (by simpa using hx)
  rw [h] at hmem
  simp [hx, Part.mem_some_iff.1 hmem]

/-! ### Fuel bounds for `const`, `id` and `curry` -/

