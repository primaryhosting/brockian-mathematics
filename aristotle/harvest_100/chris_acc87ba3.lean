import Mathlib

/-!
# No machine can always correctly predict its own next output

This file formalises the diagonal self-reference argument showing that no machine can
always correctly predict its own output before producing it.

* `Frontier.self_nonprediction_abstract` is the abstract "base case": in any system of
  machines in which the diagonal machine (the one that runs the predictor on itself and
  then outputs something different) exists, the predictor must be wrong somewhere.
* `Frontier.self_nonprediction` is the concrete instance for actual machines: for every
  *computable* predictor `P` assigning to each program `c` a guess `P c` at the value that
  `c` itself outputs (on input `0`), there is a program `c` whose own output is not
  `P c` (it either diverges or outputs a different number).  The diagonal machine is
  produced by Kleene's recursion theorem (`Nat.Partrec.Code.fixed_point`).
-/

namespace Frontier

open Nat.Partrec Nat.Partrec.Code

/-- Abstract diagonal argument: if `out` gives the output of each machine, `P` is a
predictor, and there is a machine `d` that outputs something different from `P d`
(the diagonal machine), then `P` mispredicts some machine. -/
theorem self_nonprediction_abstract {M O : Type*} (out : M → O) (P : M → O)
    (hdiag : ∃ d : M, out d ≠ P d) : ∃ m : M, P m ≠ out m := by
  obtain ⟨d, hd⟩ := hdiag
  exact ⟨d, fun h => hd h.symm⟩

/-- **No machine can always correctly predict its own next output.**

For every computable predictor `P`, which given (the code of) a machine `c` outputs a
guess `P c` for the value that `c` itself produces on input `0`, there is a machine `c`
for which the prediction fails: the computation `c 0` does not return the value `P c`
(either it diverges, or it returns a different value).

In particular, no computable predictor is correct on all machines, hence no machine can
correctly predict its own output in all cases. -/
theorem self_nonprediction {P : Code → ℕ} (hP : Computable P) :
    ∃ c : Code, eval c 0 ≠ Part.some (P c) := by
  -- The diagonal machine: on any input it outputs `P c + 1`, one more than the prediction
  -- made for it.
  have hf : Computable fun c : Code => Code.const (P c + 1) :=
    (Code.primrec_const.to_comp).comp (Primrec.succ.to_comp.comp hP)
  obtain ⟨c, hc⟩ := fixed_point hf
  refine ⟨c, ?_⟩
  have h0 : eval c 0 = Part.some (P c + 1) := by
    rw [← hc]; simp [eval_const]
  rw [h0]
  simp

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

