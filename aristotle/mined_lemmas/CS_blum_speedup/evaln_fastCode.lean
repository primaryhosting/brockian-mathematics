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


theorem evaln_fastCode : ∀ (n x k : ℕ), bud n x ≤ k → evaln k (fastCode n) x = some (gfun x) := by
  intro n
  induction n with
  | zero =>
    intro x k hk
    rw [fastCode]
    refine evaln_baseCode ?_
    have h : bud 0 x = (gfun x + 2) ^ 4 + (x + 2) ^ 4 + x + 2 := by simp [bud]
    omega
  | succ n ih =>
    intro x k hk
    have hbud0 : (gfun (x - (n + 1)) + 2) ^ 4 + (x + 2) ^ 4 + x + 2 ≤ k := hk
    have hpow : x + 2 ≤ (x + 2) ^ 4 := Nat.le_self_pow (by norm_num) _
    obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
    have hx : x ≤ K := by omega
    rw [fastCode, evaln_pair' hx, evaln_id' hx, evaln_comp' hx,
      evaln_predCode (x := x) (k := K + 1) (by omega)]
    simp only [Option.bind_some]
    have hstep : bud n (x - 1) ≤ K + 1 := by
      have h1 : x - 1 - n = x - (n + 1) := by omega
      have h2 : (x - 1 + 2) ^ 4 ≤ (x + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      simp only [bud, h1]
      omega
    rw [ih (x - 1) (K + 1) hstep]
    simp only [Seq.seq]
    exact congrArg some (gfun_eq_pair x).symm

