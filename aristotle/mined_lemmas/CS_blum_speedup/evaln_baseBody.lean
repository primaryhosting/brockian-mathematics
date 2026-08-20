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


theorem evaln_baseBody {K y g : ℕ} (hvK : Nat.pair 0 (Nat.pair y g) ≤ K)
    (hzK : Nat.pair y g ≤ K) (hyK : y ≤ K) :
    evaln (K + 1) baseBody (Nat.pair 0 (Nat.pair y g)) = some (Nat.pair (y + 1) g) := by
  have hA : evaln (K + 1) (Code.comp Code.succ (Code.comp Code.left Code.right))
      (Nat.pair 0 (Nat.pair y g)) = some (y + 1) := by
    rw [evaln_comp' hvK, evaln_comp' hvK, evaln_right' hvK]
    simp only [Nat.unpair_pair, Option.bind_some]
    rw [evaln_left' hzK]
    simp only [Nat.unpair_pair, Option.bind_some]
    exact evaln_succ' hyK
  have hB : evaln (K + 1) (Code.comp Code.right Code.right) (Nat.pair 0 (Nat.pair y g))
      = some g := by
    rw [evaln_comp' hvK, evaln_right' hvK]
    simp only [Nat.unpair_pair, Option.bind_some]
    rw [evaln_right' hzK]
    simp
  rw [baseBody, evaln_pair' hvK, hA, hB]
  simp [Seq.seq]

