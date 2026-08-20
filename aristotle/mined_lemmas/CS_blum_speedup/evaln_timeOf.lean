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


theorem evaln_timeOf {c : Code} {x v : ℕ} (h : v ∈ eval c x) :
    evaln (timeOf c x) c x = some v := by
  obtain ⟨k, hk⟩ := evaln_complete.1 h
  have hk' : evaln k c x = some v := hk
  have hne : {k | (evaln k c x).isSome}.Nonempty := ⟨k, by simp [Set.mem_setOf_eq, hk']⟩
  have hmem : (evaln (timeOf c x) c x).isSome := Nat.sInf_mem hne
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hmem
  have hw' : w ∈ eval c x := evaln_sound hw
  rw [hw, Part.mem_unique h hw']

/-! ### The programs -/

/-- Code for the constant `1`. -/
