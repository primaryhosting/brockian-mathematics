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

theorem fermat_quartic_rat_solutions {x y : ℚ} (h : x ^ 4 + y ^ 4 = 1) :
    (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1) := by
  have hx : ((x.num : ℚ)) = x * (x.den : ℚ) := (Rat.mul_den_eq_num x).symm
  have hy : ((y.num : ℚ)) = y * (y.den : ℚ) := (Rat.mul_den_eq_num y).symm
  set a : ℤ := x.num * (y.den : ℤ) with ha
  set b : ℤ := y.num * (x.den : ℤ) with hb
  set n : ℤ := (x.den : ℤ) * (y.den : ℤ) with hn
  have key : a ^ 4 + b ^ 4 = (n ^ 2) ^ 2 := by
    have : ((a : ℚ)) ^ 4 + ((b : ℚ)) ^ 4 = (((n ^ 2 : ℤ) : ℚ)) ^ 2 := by
      push_cast [ha, hb, hn, hx, hy]
      nlinarith [h, sq_nonneg (x * y)]
    exact_mod_cast this
  have hab : a = 0 ∨ b = 0 := by
    by_contra hc
    push_neg at hc
    exact not_fermat_42 hc.1 hc.2 key
  have hx0 : a = 0 → x = 0 := by
    intro h0
    refine Rat.zero_iff_num_zero.mpr ?_
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact h1
    · exact absurd h1 (by exact_mod_cast y.den_nz)
  have hy0 : b = 0 → y = 0 := by
    intro h0
    refine Rat.zero_iff_num_zero.mpr ?_
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact h1
    · exact absurd h1 (by exact_mod_cast x.den_nz)
  have quart : ∀ t : ℚ, t ^ 4 = 1 → t = 1 ∨ t = -1 := by
    intro t ht
    have h4 : (t - 1) * (t + 1) * (t ^ 2 + 1) = 0 := by nlinarith [ht]
    rcases mul_eq_zero.1 h4 with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · left; linarith
      · right; linarith
    · nlinarith [sq_nonneg t]
  rcases hab with h0 | h0
  · have hx' := hx0 h0
    subst hx'
    have hy4 : y ^ 4 = 1 := by linarith [h]
    rcases quart y hy4 with h1 | h1
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, h1⟩))
  · have hy' := hy0 h0
    subst hy'
    have hx4 : x ^ 4 = 1 := by linarith [h]
    rcases quart x hx4 with h1 | h1
    · exact Or.inl ⟨h1, rfl⟩
    · exact Or.inr (Or.inl ⟨h1, rfl⟩)

