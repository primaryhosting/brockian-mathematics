/-
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 requires module
-- doc-comments to appear *after* the `import` lines; the text is otherwise verbatim.)

import Mathlib

/-!
## Overview

The Catalan–Mihailescu theorem states that `8 = 2 ^ 3` and `9 = 3 ^ 2` are the only two
consecutive perfect powers, i.e. the only solution of `x ^ p - y ^ q = 1` in integers
`x, y, p, q > 1` is `3 ^ 2 - 2 ^ 3 = 1`.

This file formalises the statement (`Frontier.CatalanMihailescuStatement`), and proves,
axiom-cleanly:

* the base case `3 ^ 2 = 2 ^ 3 + 1`, and that `8`, `9` are perfect powers;
* a Lean-checked **reduction**: the general statement is *equivalent* to the statement
  restricted to prime exponents (`Frontier.catalan_iff_prime_exponents`);
* several complete subcases of the theorem:
  - equal exponents: `x ^ k ≠ y ^ k + 1` for `y ≥ 1`, `k ≥ 2`;
  - both exponents even: `x ^ p ≠ y ^ q + 1` for `p`, `q` even and `y > 1`;
  - even exponent against an odd base: `x ^ p ≠ y ^ q + 1` whenever `p` is even, `y` is
    odd and `y > 1`, `q ≥ 2` (in particular, in a hypothetical second solution with
    `p` even the number `y` must be even);
  - odd base with even exponent: `x ^ p ≠ y ^ q + 1` whenever `y` is odd, `q` is even
    and `p ≥ 2`;
* a kernel-checked finite verification: `9` and `8` are the only consecutive perfect powers
  up to `1000`.

The main theorem `Frontier.Catalan_Mihailescu` packages these results.
-/

namespace Frontier

/-- `n` is a perfect power: `n = a ^ k` with `a > 1` and `k > 1`. -/

theorem catalan_iff_prime_exponents :
    CatalanMihailescuStatement ↔ CatalanMihailescuPrimeStatement := by
  constructor
  · intro H x y p q hx hy hp hq heq
    obtain ⟨h9, h8⟩ := H (x ^ p) (y ^ q) ⟨x, p, hx, hp.one_lt, rfl⟩ ⟨y, q, hy, hq.one_lt, rfl⟩ heq
    obtain ⟨hx3, hp2⟩ := pow_eq_nine hx hp.two_le h9
    obtain ⟨hy2, hq3⟩ := pow_eq_eight hy hq.two_le h8
    exact ⟨hx3, hp2, hy2, hq3⟩
  · intro H m n hm hn hmn
    obtain ⟨x, p, hx, hp, rfl⟩ := (isPerfectPower_iff_prime_exponent m).mp hm
    obtain ⟨y, q, hy, hq, rfl⟩ := (isPerfectPower_iff_prime_exponent n).mp hn
    obtain ⟨hx3, hp2, hy2, hq3⟩ := H x y p q hx hy hp hq hmn
    subst hx3; subst hp2; subst hy2; subst hq3
    norm_num

/-! ### Complete subcases -/

/-- Two consecutive perfect powers cannot have the same exponent. -/
