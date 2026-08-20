import RequestProject.DiophAux

/-!
# Davis' bounded universal quantifier

This file proves that bounded universal quantification preserves Diophantine sets:
if `S` is Diophantine, so is `{v | ∀ x < f v, (x, v) ∈ S}`.
-/

open Dioph Nat Sum

namespace CS

variable {α : Type} {n : ℕ}

/-- The bound `B` used in Davis' construction: it dominates the value of the majorant `q`
at the extreme arguments, as well as `y` and `u`. -/

theorem hilbert10_undecidable_int :
    ∃ (n : ℕ) (Q : MvPolynomial (Fin (n + 1)) ℤ),
      ¬ ComputablePred fun a : ℕ => ∃ y : Fin n → ℤ,
          MvPolynomial.eval (Fin.cons (a : ℤ) y) Q = 0 := by
  obtain ⟨m, P, hP⟩ := exists_poly_of_dioph Halts (dioph_of_rePred Halts halts_re)
  refine ⟨m * 4, bind₁ fourSq P, fun h => halts_not_computable (ComputablePred.of_eq h ?_)⟩
  intro a
  rw [exists_int_iff_exists_nat]
  exact hP a

end CS

import Mathlib

/-!
# Auxiliary Diophantine machinery towards the MRDP theorem

This file develops arithmetic tools used in the proof that every recursively enumerable
predicate is Diophantine (the MRDP theorem), on top of Mathlib's `Dioph` API and
Matiyasevich's theorem `Dioph.pow_dioph`.

The main ingredients are:

* `CS.choose_eq_div_mod` / `CS.choose_dioph`: binomial coefficients are Diophantine;
* `CS.factorial_eq_div` / `CS.factorial_dioph`: the factorial is Diophantine;
* `CS.prime_dioph`: primality is Diophantine (via Wilson's theorem);
* `CS.exists_crt_code`: Gödel-style coding of a finite sequence with a common modulus base;
* `CS.poly_int_modEq`: polynomials respect congruences;
* `CS.exists_majorant`: every polynomial admits a monotone nonnegative majorant;
* `CS.dioph_fin`: a Diophantine set can be described with finitely many witness variables.

The bounded universal quantifier itself is proved in `RequestProject.Davis`.
-/

open Dioph Nat

namespace CS

/-! ### Binomial coefficients -/

/-- Digit extraction formula for binomial coefficients: writing `(u+1)^n` in base `u` exposes
the binomial coefficients `n.choose k` as its digits, as soon as `2 ^ n < u`. -/
