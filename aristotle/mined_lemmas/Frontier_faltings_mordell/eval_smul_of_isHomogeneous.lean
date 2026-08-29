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

theorem eval_smul_of_isHomogeneous {σ R : Type*} [CommSemiring R] {f : MvPolynomial σ R} {d : ℕ}
    (hf : f.IsHomogeneous d) (c : R) (x : σ → R) :
    eval (c • x) f = c ^ d * eval x f := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hd : ∑ i ∈ e.support, e i = d := by
    have := hf (mem_support_iff.mp he)
    rw [← this]; simp [Finsupp.weight_apply, Finsupp.sum]
  have h2 : ∏ i ∈ e.support, (c • x) i ^ e i
      = (∏ i ∈ e.support, c ^ e i) * ∏ i ∈ e.support, x i ^ e i := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by simp [mul_pow]
  rw [h2, Finset.prod_pow_eq_pow_sum, hd]; ring

/-- The set of rational points of the plane projective curve cut out by `f`, as a subset of
the projective plane `ℙ²(ℚ)`.  (For homogeneous `f` of positive degree this is independent of
the chosen representatives; see `Frontier.mem_projectivePoints_mk`.) -/
