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
