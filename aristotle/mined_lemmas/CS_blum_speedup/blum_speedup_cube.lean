/-
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header above is a plain
-- block comment; its text is otherwise verbatim.)

import Mathlib

/-!
We work with Mathlib's model of computation `Nat.Partrec.Code` together with its canonical
step-indexed evaluator `Nat.Partrec.Code.evaln`.  The running time of a program `c` on input `x`
is the least step bound `k` for which `evaln k c x` returns a value.

We exhibit an explicit total computable function `gfun` (a doubly exponentially growing function)
with *no fastest program*: for every program `c` computing `gfun` there is another program `d`
computing `gfun` which is strictly faster on all but finitely many inputs.
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-! ### Elementary arithmetic helpers -/


theorem blum_speedup_cube :
    ∃ f : ℕ → ℕ,
      (∃ c : Code, eval c = fun x => Part.some (f x)) ∧
      ∀ c : Code, eval c = (fun x => Part.some (f x)) →
        ∃ d : Code, eval d = (fun x => Part.some (f x)) ∧
          ∀ᶠ x in Filter.atTop, timeOf d x ^ 3 ≤ timeOf c x := by
  refine ⟨gfun, ⟨fastCode 0, eval_fastCode 0⟩, fun c hc => ⟨fastCode (cdepth c + 8),
    eval_fastCode _, ?_⟩⟩
  rw [Filter.eventually_atTop]
  exact ⟨2 * (cdepth c + 8) + 60, fun x hx => (speedup_core hc x hx).1⟩

end CS

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

