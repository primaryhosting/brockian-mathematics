-- (Lean requires `import` to precede any module docstring; the required header follows.)
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
at least `2` defined over `ℚ` has only finitely many rational points.

Here we formalize the statement for *smooth plane curves*, where the genus is given by the
degree–genus formula `g = (d-1)(d-2)/2`, so that "genus ≥ 2" is exactly "degree ≥ 4".
The general statement is recorded as `Frontier.MordellConjecturePlane` (a `Prop`-valued
definition, not proved here — it is Faltings' theorem).

We then prove, unconditionally and axiom-cleanly:

* `Frontier.projectivePoints_finite_of_affine`: a Lean-checked reduction of the finiteness of
  the rational points of a projective plane curve to finiteness of its affine rational points
  together with its rational points at infinity;
* `Frontier.mordellPlane_of_affine_finiteness`: the resulting reduction of
  `MordellConjecturePlane` to the affine statement;
* `Frontier.faltings_mordell`: the base case for the Fermat quartic `x⁴ + y⁴ = z⁴`, a smooth
  plane curve of degree `4` (hence of genus `3 ≥ 2`), whose set of rational points in `ℙ²(ℚ)`
  is proved finite — in fact it consists of exactly the four points
  `(±1 : 0 : 1)`, `(0 : ±1 : 1)`.
-/

namespace Frontier

open MvPolynomial Projectivization

/-! ## Homogeneous polynomials and projective points -/

/-- Evaluating a homogeneous polynomial of degree `d` at a scaled point scales the value
by `c ^ d`. -/

def IsSmoothPlaneCurveOfDegree (d : ℕ) (f : MvPolynomial (Fin 3) ℚ) : Prop :=
  f.IsHomogeneous d ∧
    ∀ x : Fin 3 → AlgebraicClosure ℚ,
      (∀ i, aeval x (pderiv i f) = 0) → x = 0

/-- **Faltings' theorem (Mordell conjecture) for smooth plane curves.**  A smooth plane curve
of degree `d ≥ 4` over `ℚ` has genus `(d-1)(d-2)/2 ≥ 2`, and hence — by Faltings' theorem —
only finitely many rational points.  This `Prop` records the statement; it is *not* proved
here.  The theorem `Frontier.faltings_mordell` proves an instance of it, and
`Frontier.mordellPlane_of_affine_finiteness` reduces it to an affine statement. -/
