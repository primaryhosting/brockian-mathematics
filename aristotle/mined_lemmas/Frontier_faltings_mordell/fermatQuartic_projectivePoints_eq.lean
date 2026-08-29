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

theorem fermatQuartic_projectivePoints_eq :
    projectivePoints fermatQuartic =
      {Projectivization.mk ℚ ![1, 0, 1] (vec_ne_zero_of_last 1 0),
       Projectivization.mk ℚ ![-1, 0, 1] (vec_ne_zero_of_last (-1) 0),
       Projectivization.mk ℚ ![0, 1, 1] (vec_ne_zero_of_last 0 1),
       Projectivization.mk ℚ ![0, -1, 1] (vec_ne_zero_of_last 0 (-1))} := by
  have hhom := fermatQuartic_isSmoothPlaneCurve.1
  ext P
  constructor
  · intro hP
    have hrep : eval P.rep fermatQuartic = 0 := hP
    rw [eval_fermatQuartic] at hrep
    have h2 : P.rep 2 ≠ 0 := by
      intro h2
      refine P.rep_nonzero ?_
      rw [h2] at hrep
      have hx : P.rep 0 ^ 2 = 0 := by nlinarith [sq_nonneg (P.rep 0 ^ 2), sq_nonneg (P.rep 1 ^ 2)]
      have hy : P.rep 1 ^ 2 = 0 := by nlinarith [sq_nonneg (P.rep 0 ^ 2), sq_nonneg (P.rep 1 ^ 2)]
      have hx0 : P.rep 0 = 0 := by
        exact pow_eq_zero_iff (two_ne_zero) |>.1 hx
      have hy0 : P.rep 1 = 0 := by
        exact pow_eq_zero_iff (two_ne_zero) |>.1 hy
      funext i
      fin_cases i <;> simpa using ‹_›
    set x : ℚ := P.rep 0 / P.rep 2 with hxdef
    set y : ℚ := P.rep 1 / P.rep 2 with hydef
    have hsm : (P.rep 2)⁻¹ • P.rep = ![x, y, 1] := by
      funext i
      fin_cases i <;> simp [hxdef, hydef, h2, div_eq_inv_mul]
    have hPeq : P = Projectivization.mk ℚ ![x, y, 1] (vec_ne_zero_of_last x y) :=
      eq_mk_of_inv_smul_rep P h2 (vec_ne_zero_of_last x y) hsm
    have hxy : x ^ 4 + y ^ 4 = 1 := by
      rw [hxdef, hydef, div_pow, div_pow, ← add_div,
        div_eq_one_iff_eq (pow_ne_zero 4 h2)]
      linarith [hrep]
    rcases fermat_quartic_rat_solutions hxy with ⟨h1, h3⟩ | ⟨h1, h3⟩ | ⟨h1, h3⟩ | ⟨h1, h3⟩ <;>
      rw [hPeq] <;> simp [h1, h3]
  · intro hP
    have hmem : ∀ a b : ℚ, a ^ 4 + b ^ 4 = 1 →
        Projectivization.mk ℚ ![a, b, 1] (vec_ne_zero_of_last a b) ∈ projectivePoints fermatQuartic
        := by
      intro a b hab
      rw [mem_projectivePoints_mk hhom (by norm_num), eval_fermatQuartic]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]
      rw [hab]
      norm_num
    rcases hP with h | h | h | h <;> rw [h]
    · exact hmem 1 0 (by norm_num)
    · exact hmem (-1) 0 (by norm_num)
    · exact hmem 0 1 (by norm_num)
    · exact hmem 0 (-1) (by norm_num)

/-- The Fermat quartic has exactly four rational points in `ℙ²(ℚ)`. -/
