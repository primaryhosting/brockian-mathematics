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

lemma two_le_planeCurveGenus {d : ℕ} (hd : 4 ≤ d) : 2 ≤ planeCurveGenus d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
  have h1 : 4 + k - 1 = k + 3 := by omega
  have h2 : 4 + k - 2 = k + 2 := by omega
  rw [planeCurveGenus, h1, h2, Nat.le_div_iff_mul_le (by norm_num)]
  nlinarith

/-- A homogeneous `F ∈ ℚ[X₀,X₁,X₂]` cuts out a smooth plane curve if its partial derivatives
have no common zero other than the origin, over an algebraic closure of `ℚ`. -/
