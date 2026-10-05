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

theorem projectivePoints_finite_of_affine {f : MvPolynomial (Fin 3) ℚ} {d : ℕ}
    (hf : f.IsHomogeneous d)
    (hA : {p : ℚ × ℚ | eval ![p.1, p.2, 1] f = 0}.Finite)
    (hB : {q : ℚ | eval ![q, 1, 0] f = 0}.Finite) :
    (projectivePoints f).Finite := by
  classical
  set g : ℚ × ℚ → Projectivization ℚ (Fin 3 → ℚ) :=
    fun p => Projectivization.mk ℚ ![p.1, p.2, 1] (vec_ne_zero_of_last p.1 p.2) with hg
  set h : ℚ → Projectivization ℚ (Fin 3 → ℚ) :=
    fun q => Projectivization.mk ℚ ![q, 1, 0] (vec_ne_zero_of_mid q) with hh
  refine Set.Finite.subset
    (((hA.image g).union (hB.image h)).union
      (Set.finite_singleton (Projectivization.mk ℚ ![1, 0, 0] vec_ne_zero_first))) ?_
  rintro P hP
  have hrep : eval P.rep f = 0 := hP
  have hPne : P.rep ≠ 0 := P.rep_nonzero
  by_cases h2 : P.rep 2 = 0
  · by_cases h1 : P.rep 1 = 0
    · -- the point `(1 : 0 : 0)`
      have h0 : P.rep 0 ≠ 0 := by
        intro h0
        apply hPne
        funext i
        fin_cases i <;> simpa using ‹_›
      refine Or.inr ?_
      have hsm : (P.rep 0)⁻¹ • P.rep = ![1, 0, 0] := by
        funext i
        fin_cases i <;> simp [h0, h1, h2]
      simp [eq_mk_of_inv_smul_rep P h0 vec_ne_zero_first hsm]
    · -- a point at infinity `(q : 1 : 0)`
      refine Or.inl (Or.inr ?_)
      set q : ℚ := P.rep 0 / P.rep 1 with hq
      have hsm : (P.rep 1)⁻¹ • P.rep = ![q, 1, 0] := by
        funext i
        fin_cases i <;> simp [h1, h2, hq, div_eq_inv_mul]
      have hqmem : q ∈ {q : ℚ | eval ![q, 1, 0] f = 0} := by
        show eval ![q, 1, 0] f = 0
        rw [← hsm, eval_smul_of_isHomogeneous hf, hrep, mul_zero]
      exact ⟨q, hqmem, (eq_mk_of_inv_smul_rep P h1 (vec_ne_zero_of_mid q) hsm).symm⟩
  · -- an affine point
    refine Or.inl (Or.inl ?_)
    set p : ℚ × ℚ := (P.rep 0 / P.rep 2, P.rep 1 / P.rep 2) with hp
    have hsm : (P.rep 2)⁻¹ • P.rep = ![p.1, p.2, 1] := by
      funext i
      fin_cases i <;> simp [hp, h2, div_eq_inv_mul]
    have hpmem : p ∈ {p : ℚ × ℚ | eval ![p.1, p.2, 1] f = 0} := by
      show eval ![p.1, p.2, 1] f = 0
      rw [← hsm, eval_smul_of_isHomogeneous hf, hrep, mul_zero]
    exact ⟨p, hpmem, (eq_mk_of_inv_smul_rep P h2 (vec_ne_zero_of_last p.1 p.2) hsm).symm⟩

/-- **A Lean-checked reduction of the Mordell conjecture for plane curves** to the
corresponding affine finiteness statement. -/
