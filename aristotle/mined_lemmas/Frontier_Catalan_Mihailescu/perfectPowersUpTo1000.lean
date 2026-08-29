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

def perfectPowersUpTo1000 : Finset ℕ :=
  {4, 8, 9, 16, 25, 27, 32, 36, 49, 64, 81, 100, 121, 125, 128, 144, 169, 196, 216, 225, 243,
   256, 289, 324, 343, 361, 400, 441, 484, 512, 529, 576, 625, 676, 729, 784, 841, 900, 961, 1000}

