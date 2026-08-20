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


theorem timeOf_lower_bound {c : Code} (hc : eval c = fun x => Part.some (gfun x)) (x : ℕ)
    (hx : cdepth c + 1 ≤ x) : 2 ^ 2 ^ (x - 1 - cdepth c) ≤ timeOf c x + 2 := by
  have hmem : gfun x ∈ eval c x := by rw [hc]; exact Part.mem_some _
  have hev : evaln (timeOf c x) c x = some (gfun x) := evaln_timeOf hmem
  have hout : gfun x + 2 ≤ (timeOf c x + 2) ^ 2 ^ cdepth c :=
    evaln_output_bound _ _ _ _ hev
  have hlow : 2 ^ 2 ^ (x - 1) ≤ gfun x := by
    have h := tower_le_gfun (x - 1)
    rwa [show x - 1 + 1 = x by omega] at h
  by_contra hcon
  push_neg at hcon
  have hpow : (timeOf c x + 2) ^ 2 ^ cdepth c < (2 ^ 2 ^ (x - 1 - cdepth c)) ^ 2 ^ cdepth c :=
    Nat.pow_lt_pow_left hcon (by positivity)
  have hexp : (2 ^ 2 ^ (x - 1 - cdepth c) : ℕ) ^ 2 ^ cdepth c = 2 ^ 2 ^ (x - 1) := by
    rw [← pow_mul, ← pow_add]
    congr 2
    omega
  rw [hexp] at hpow
  omega

/-! ### Upper bound on the running time of the fast programs -/

