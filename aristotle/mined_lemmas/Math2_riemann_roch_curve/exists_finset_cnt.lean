/-
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring; the required header is
-- reproduced verbatim as the module docstring immediately below the import.)

import RequestProject.Math2.Canonical

/-!
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Statement

For a smooth projective curve, described here through its function field `F / K` with its
family of places `P` (see `Math2.PreCurve` and `Math2.PreCurve.IsCurve`), there exists a
*canonical divisor* `W` such that for every divisor `D`

  `ℓ(D) - ℓ(W - D) = deg D + 1 - g`,

where `ℓ(D) = dim_K L(D)` is the dimension of the Riemann-Roch space of `D`, `deg D` is the
degree of `D` and `g` is the genus of the curve.  The canonical divisor moreover satisfies
`ℓ(W) = g` and `deg W = 2g - 2`.
-/

namespace Math2

open PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]

/-- **Riemann-Roch for a smooth projective curve.**

There is a canonical divisor `W` (of degree `2g - 2` and with `ℓ(W) = g`) such that for every
divisor `D` on the curve,
`ℓ(D) - ℓ(W - D) = deg D + 1 - g`. -/

lemma exists_finset_cnt (a : K[X]) (ha : a ≠ 0) :
    ∃ S : Finset (FinPlace K), ∀ q : FinPlace K, q ∉ S → cnt q a = 0 := by
  classical
  refine UniqueFactorizationMonoid.induction_on_prime
    (P := fun a : K[X] => a ≠ 0 → ∃ S : Finset (FinPlace K), ∀ q : FinPlace K, q ∉ S → cnt q a = 0)
    a (fun h => absurd rfl h) (fun u hu _ => ⟨∅, fun q _ => cnt_of_isUnit q hu⟩) ?_ ha
  intro b p hb hp ih _
  obtain ⟨S, hS⟩ := ih hb
  have hpne : p ≠ 0 := hp.ne_zero
  have hunit : IsUnit (C (p.leadingCoeff⁻¹) : K[X]) :=
    isUnit_C.2 (Ne.isUnit (inv_ne_zero (leadingCoeff_ne_zero.2 hpne)))
  have hassoc0 : Associated p (p * C (p.leadingCoeff⁻¹)) :=
    (associated_mul_isUnit_right_iff hunit).2 (Associated.refl p)
  refine ⟨insert ⟨p * C (p.leadingCoeff⁻¹), monic_mul_leadingCoeff_inv hpne,
    hassoc0.irreducible hp.irreducible⟩ S, ?_⟩
  intro q hq
  have hqS : q ∉ S := fun h => hq (Finset.mem_insert_of_mem h)
  have hqp : q.poly ≠ p * C (p.leadingCoeff⁻¹) := fun h =>
    hq (by rw [Finset.mem_insert]; exact Or.inl (FinPlace.ext' h))
  rw [cnt_mul q hpne hb, hS q hqS, add_zero]
  refine cnt_eq_zero_of_not_dvd q fun hdvd => hqp ?_
  have hassoc : Associated q.poly p := q.irred.associated_of_dvd hp.irreducible hdvd
  exact Polynomial.eq_of_monic_of_associated q.monic (monic_mul_leadingCoeff_inv hpne)
    (hassoc.trans hassoc0)

end P1

end Math2

/-
Strong approximation for the projective line: every adele is congruent, modulo the
everywhere-integral adeles, to a (diagonal) rational function.  Equivalently
`A(0) + F = A`, so that `H¹(0) = 0`.
-/
import RequestProject.P1.Residue

namespace Math2

namespace P1

open Polynomial RatFunc Module Submodule

universe u

variable {K : Type u} [Field K]

