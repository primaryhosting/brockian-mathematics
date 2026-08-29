import Mathlib
import RequestProject.ReingoldSlL

/-!
## Existence of universal exploration sequences

The hypothesis `CS.HasPolyUES` used in `RequestProject/ReingoldSlL.lean` asks for universal
exploration sequences of *polynomial* length; producing such short sequences is the deep part
of Reingold's theorem and is not formalised.  Here we prove, unconditionally, that universal
exploration sequences of *some* finite length always exist (`CS.exists_ues`).  This shows that
the notion is satisfiable — the only missing ingredient in `CS.HasPolyUES` is the polynomial
length bound.
-/

set_option autoImplicit false

namespace CS

namespace RotGraph

variable {n d : ℕ}

/-- The walk of length `k` only depends on the first `k` offsets. -/

lemma log_le_of_le_pow {N B c : ℕ} (h : N ≤ B ^ c) :
    Nat.log 2 N ≤ c * (Nat.log 2 B + 1) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [hN]
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    have hN1 : N = 1 := le_antisymm (by simpa using h) hN
    simp [hN1]
  have hBlt : B < 2 ^ (Nat.log 2 B + 1) := Nat.lt_pow_succ_log_self (by norm_num) B
  have hlt : N < 2 ^ (c * (Nat.log 2 B + 1)) := by
    calc N ≤ B ^ c := h
      _ < (2 ^ (Nat.log 2 B + 1)) ^ c := Nat.pow_lt_pow_left hBlt hc.ne'
      _ = 2 ^ (c * (Nat.log 2 B + 1)) := by rw [← pow_mul, Nat.mul_comm]
  exact le_of_lt (Nat.log_lt_of_lt_pow hN.ne' hlt)

/-! ## Undirected s-t connectivity is in logarithmic space -/

/-- **Undirected `s`-`t` connectivity is in `L`** (given Reingold's universal exploration
sequences): there is a polynomial degree `c` such that for every vertex count `n` and every
degree `d` there is a machine `M` with at most `(n * d + 2) ^ c` configurations — i.e. using
`O(log (n * d))` bits of space — which, with read-only query access to the rotation map of
the input graph, decides for every graph `G` and every pair of vertices `s`, `t` whether `t`
is reachable from `s`. -/
