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


theorem bud_le_tower (n x : ℕ) (hx : 2 * n + 60 ≤ x) : bud n x ≤ 2 ^ 2 ^ (x - n + 5) := by
  set m := x - n with hm
  have hmn : n + 60 ≤ m := by omega
  have hxm : x ≤ 2 * m := by omega
  -- the first summand
  have h1 : gfun m + 2 ≤ 2 ^ 2 ^ (m + 2) := by have := gfun_le_tower m; omega
  have h2 : (gfun m + 2) ^ 4 ≤ 2 ^ 2 ^ (m + 4) := by
    calc (gfun m + 2) ^ 4 ≤ (2 ^ 2 ^ (m + 2)) ^ 4 := Nat.pow_le_pow_left h1 4
      _ = 2 ^ (2 ^ (m + 2) * 4) := by rw [← pow_mul]
      _ = 2 ^ 2 ^ (m + 4) := by
            congr 1
            have h : (2 : ℕ) ^ (m + 4) = 2 ^ (m + 2) * 4 := by
              rw [show m + 4 = (m + 2) + 2 by omega, pow_add]; norm_num
            omega
  -- the polynomial summand
  have h3 : (x + 2) ^ 4 + x + 2 ≤ 2 ^ x := by
    have := quartic_le_two_pow x (by omega)
    omega
  have h4 : x ≤ 2 ^ (m + 4) := by
    have h5 : 2 * m ≤ 2 ^ m := two_mul_le_two_pow m (by omega)
    have h6 : (2 : ℕ) ^ m ≤ 2 ^ (m + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h7 : (2 : ℕ) ^ x ≤ 2 ^ 2 ^ (m + 4) := Nat.pow_le_pow_right (by norm_num) h4
  -- combine
  have h8 : (2 : ℕ) ^ 2 ^ (m + 4) + 2 ^ 2 ^ (m + 4) ≤ 2 ^ 2 ^ (m + 5) := by
    have h9 : (2 : ℕ) ^ 2 ^ (m + 4) + 2 ^ 2 ^ (m + 4) = 2 ^ (2 ^ (m + 4) + 1) := by
      rw [pow_succ]; ring
    rw [h9]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have h10 : (2 : ℕ) ^ (m + 5) = 2 ^ (m + 4) * 2 := by rw [pow_succ]
    have h11 : 1 ≤ (2 : ℕ) ^ (m + 4) := Nat.one_le_two_pow
    omega
  have hb : bud n x = (gfun m + 2) ^ 4 + ((x + 2) ^ 4 + x + 2) := by simp only [bud, hm]; ring
  rw [hb, show x - n + 5 = m + 5 from rfl]
  omega

/-! ### Main theorem -/

/-- The heart of the matter: for every program `c` computing `gfun`, the program
`fastCode (cdepth c + 8)` also computes `gfun` and is, on all large inputs, faster than `c`;
in fact even the cube of its running time is at most the running time of `c`. -/
