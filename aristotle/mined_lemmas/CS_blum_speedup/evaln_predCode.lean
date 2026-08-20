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


theorem evaln_predCode {x k : ℕ} (h : (x + 2) ^ 4 + x + 2 ≤ k) :
    evaln k predCode x = some (x - 1) := by
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
  have hpow : x + 2 ≤ (x + 2) ^ 4 := Nat.le_self_pow (by norm_num) _
  have hx : x ≤ K := by omega
  rw [predCode, evaln_comp' hx, evaln_pair' hx, evaln_zero' hx, evaln_id' hx]
  simp only [Seq.seq]
  exact evaln_predLoop x (K + 1) h

