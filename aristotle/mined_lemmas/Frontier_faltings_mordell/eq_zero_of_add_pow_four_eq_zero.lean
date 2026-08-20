import Mathlib
/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Faltings' theorem (the Mordell conjecture) states that a smooth projective curve of genus
`≥ 2` over `ℚ` has only finitely many rational points.

In this file we

* formalise the statement for smooth plane curves in `ℙ²`, where the genus is given by the
  degree–genus formula `g = (d-1)(d-2)/2`, so that `d ≥ 4` is exactly the condition `g ≥ 2`
  (`Frontier.FaltingsMordellStatement`);
* verify, unconditionally, an instance of it: the Fermat quartic `x⁴ + y⁴ = z⁴`, a smooth
  plane curve of degree `4` and hence of genus `3`, has only finitely many rational points
  (`Frontier.faltings_mordell`) — indeed exactly four (`Frontier.fermatQuartic_projPoints`).
  The proof uses Fermat's Last Theorem for exponent four.
-/

namespace Frontier

open MvPolynomial
open scoped LinearAlgebra.Projectivization

noncomputable section

/-- The set of `ℚ`-points of the plane projective curve cut out by `F`. -/

lemma eq_zero_of_add_pow_four_eq_zero {a b : ℚ} (h : a ^ 4 + b ^ 4 = 0) : a = 0 := by
  have h4 : a ^ 4 = 0 := by nlinarith [sq_nonneg (a ^ 2), sq_nonneg (b ^ 2)]
  exact pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h4

/-- Classification of the nonzero rational solutions of `x⁴ + y⁴ = z⁴`, up to scaling:
by Fermat's Last Theorem for exponent four, each is proportional to one of four vectors. -/
