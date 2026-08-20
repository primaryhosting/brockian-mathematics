import Mathlib

/-!
# Further Diophantine functions: binomial coefficients and factorials

Mathlib's `Mathlib/NumberTheory/Dioph.lean` develops the basic theory of Diophantine sets and
functions and culminates in Matiyasevich's theorem that exponentiation is Diophantine
(`Dioph.pow_dioph`).  Two further classical steps on the way to the MRDP theorem are formalized
here, both unconditionally:

* `CS.choose_dioph`: the binomial coefficient `(n, k) ↦ n.choose k` is a Diophantine function.
  This follows from `Dioph.pow_dioph` because `n.choose k` is the `k`-th digit of `(u + 1) ^ n`
  in base `u := 2 ^ n + 1`, and division and remainder are Diophantine.
* `CS.factorial_dioph`: the factorial `r ↦ r !` is a Diophantine function.  This follows from
  `CS.choose_dioph` because `r ! = u ^ r / u.choose r` as soon as `u` is large enough compared
  to `r`, and `u := (2 * r) ^ (r + 2) + 2 * r + 1` is large enough.
-/

set_option autoImplicit false

namespace CS

open Finset Nat

/-! ## Digits in base `u` -/

/-- A number with all digits `< u` and at most `k` digits is `< u ^ k`. -/

def MRDP : Prop :=
  ∀ S : Set ℕ, REPred S → Dioph {v : Fin 1 → ℕ | S (v 0)}

/-! ## Hilbert's tenth problem is undecidable -/

/-- **Hilbert's tenth problem is undecidable.**

Given the MRDP theorem, there is a single integer polynomial `p` in one distinguished parameter
`a` and finitely many further unknowns `t` such that no algorithm decides, given `a`, whether the
Diophantine equation `p (a, t) = 0` has a solution `t` in the natural numbers.  In particular
there is no algorithm deciding solvability of arbitrary Diophantine equations. -/
