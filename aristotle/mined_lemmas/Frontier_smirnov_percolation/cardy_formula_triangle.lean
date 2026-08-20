import Mathlib

/-!
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Cardy–Smirnov theory says that the scaling limit of crossing probabilities for critical
site percolation on the triangular lattice is *conformally invariant*, and that in the
reference domain — Carleson's equilateral triangle — the limiting crossing probability is
the linear (barycentric) function, so that the crossing probability between the side `AB`
and the sub-segment `CX` of the side `CA` equals `|CX| / |CA|`.

This file formalizes the two structural halves of that statement and proves them:

* **Conformal invariance / reduction.** The conformal modulus of a configuration of four
  marked boundary points is the cross-ratio; it is invariant under Möbius transformations,
  hence any crossing functional that is a function of the modulus is conformally invariant.
  This is the reduction step: the whole Cardy–Smirnov formula is determined by its value on
  one reference configuration.

* **Base case (Carleson's equilateral triangle).** The three Cardy–Smirnov functions
  `smirnovA, smirnovB, smirnovC` attached to the equilateral triangle with vertices
  `A = 0`, `B = 1`, `C = 1/2 + i √3 / 2` are harmonic on the whole plane, sum to `1`,
  take the value `1` at their own vertex and vanish on the opposite side, and satisfy
  Cardy's formula `smirnovA X = |CX| / |CA|` for `X` on the side `CA`.

The probabilistic input of Smirnov's theorem (existence of the scaling limit for critical
site percolation on the triangular lattice) is *not* formalized here; what is formalized
and proved is the conformal-invariance reduction together with the closed form of the
limit in the reference triangle.
-/

namespace Frontier

open Complex

/-! ### The conformal modulus of four marked boundary points -/

/-- The cross-ratio of four points of the plane.  For a Jordan domain with four marked
boundary points this is the conformal modulus of the configuration. -/

theorem cardy_formula_triangle {t : ℝ} (ht₀ : 0 ≤ t) :
    smirnovA (vC + (t : ℂ) * (vA - vC)) = dist vC (vC + (t : ℂ) * (vA - vC)) / dist vC vA ∧
      smirnovA (vC + (t : ℂ) * (vA - vC)) = t := by
  have h3 : (Real.sqrt 3 : ℝ) ≠ 0 := sqrt3_ne_zero
  have hC : vC ≠ 0 := by
    intro h
    have : (Real.sqrt 3 / 2 : ℝ) = 0 := by
      simpa [vC, Complex.ext_iff] using congrArg Complex.im h
    exact h3 (by linarith [this])
  have hval : smirnovA (vC + (t : ℂ) * (vA - vC)) = t := by
    rw [smirnovA_apply]
    simp only [vA, vC, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.zero_re, Complex.zero_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    ring
  refine ⟨?_, hval⟩
  have hdist : dist vC (vC + (t : ℂ) * (vA - vC)) = t * dist vC vA := by
    have h1 : vC - (vC + (t : ℂ) * (vA - vC)) = (t : ℂ) * (vC - vA) := by ring
    rw [dist_eq_norm, dist_eq_norm, h1, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ht₀]
  rw [hval, hdist, mul_div_assoc, div_self, mul_one]
  simpa [dist_eq_norm, vA, sub_zero, sub_eq_zero] using hC

/-! ### Main statement -/

/--
**Cardy–Smirnov: conformal invariance of critical percolation crossing probabilities.**

The statement is the conjunction of the conformal-invariance reduction and of Smirnov's
base case in Carleson's equilateral triangle:

0. the reference triangle `A B C` is equilateral with unit sides;
1. the conformal modulus (cross-ratio) of four marked boundary points is invariant under
   Möbius transformations;
2. consequently every crossing functional that is a function of the modulus is conformally
   invariant, so the crossing probability is determined by its values on one reference
   family of configurations;
3. the three Cardy–Smirnov functions of the reference equilateral triangle are harmonic on
   the plane and sum to `1`;
4. `smirnovA` equals `1` at `A` and vanishes identically on the opposite side `BC`;
5. Cardy's formula holds in the reference triangle: for `X = C + t (A - C)` on the side
   `CA` with `t ∈ [0,1]`, the crossing function equals the ratio `|CX| / |CA|` (and equals
   `t`).
-/
