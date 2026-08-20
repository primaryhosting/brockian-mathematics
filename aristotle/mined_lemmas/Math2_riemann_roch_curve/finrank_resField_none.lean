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

lemma finrank_resField_none :
    finrank K ((projectiveLine K).resField (none : Place K)) = 1 := by
  have hinj : Function.Injective (constToRes (K := K)) := by
    intro c d hcd
    by_contra hne
    have hsub : c - d ≠ 0 := sub_ne_zero.2 hne
    have h0 : constToRes (c - d) = 0 := by
      rw [map_sub, hcd, sub_self]
    rw [constToRes, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, mem_maxIdeal_iff] at h0
    have hcoe : ((constToLocal (c - d) : ↥((projectiveLine K).valSub (none : Place K) 0)) :
        RatFunc K) = algebraMap K (RatFunc K) (c - d) := rfl
    rw [hcoe] at h0
    have hinj0 : Function.Injective (algebraMap K (RatFunc K)) :=
      (algebraMap K (RatFunc K)).injective
    have hne0 : algebraMap K (RatFunc K) (c - d) ≠ 0 := fun hh =>
      hsub (hinj0 (hh.trans (map_zero _).symm))
    rcases h0 with h | h
    · exact hne0 h
    · rw [RatFunc.algebraMap_eq_C] at h
      simp only [ordZP, ordInfZ, RatFunc.intDegree_C] at h
      omega
  have hsurj : Function.Surjective (constToRes (K := K)) := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective ((projectiveLine K).maxIdeal (none : Place K)) y
    obtain ⟨x, hx⟩ := x
    rcases eq_or_ne x 0 with rfl | hx0
    · refine ⟨0, ?_⟩
      rw [constToRes, LinearMap.comp_apply, map_zero]
      rfl
    · have hord : (0 : ℤ) ≤ ordZP (none : Place K) x := by
        rcases (mem_valSub_iff' (none : Place K) 0 x).1 hx with h | h
        · exact absurd h hx0
        · exact h
      have hdeg : x.num.natDegree ≤ x.denom.natDegree := by
        simp only [ordZP, ordInfZ, RatFunc.intDegree] at hord
        omega
      have hnum : x.num ≠ 0 := RatFunc.num_ne_zero hx0
      have hden : x.denom ≠ 0 := RatFunc.denom_ne_zero x
      have hdenne : algebraMap K[X] (RatFunc K) x.denom ≠ 0 := fun hh =>
        hden (RatFunc.algebraMap_injective K (hh.trans (map_zero _).symm))
      have key : ∀ c : K, (algebraMap K (RatFunc K) c - x = 0 ∨
          1 ≤ ordZP (none : Place K) (algebraMap K (RatFunc K) c - x)) →
          constToRes c = Submodule.Quotient.mk ⟨x, hx⟩ := by
        intro c hc
        rw [constToRes, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
          mem_maxIdeal_iff]
        have hcoe : ((constToLocal c - ⟨x, hx⟩ :
            ↥((projectiveLine K).valSub (none : Place K) 0)) : RatFunc K)
            = algebraMap K (RatFunc K) c - x := rfl
        rw [hcoe]
        exact hc
      rcases lt_or_eq_of_le hdeg with hlt | heq
      · refine ⟨0, key 0 (Or.inr ?_)⟩
        rw [map_zero, zero_sub]
        have hnegd : ordZP (none : Place K) (-x) = ordZP (none : Place K) x := by
          simp only [ordZP, ordInfZ, RatFunc.intDegree_neg]
        rw [hnegd]
        simp only [ordZP, ordInfZ, RatFunc.intDegree]
        omega
      · set c : K := x.num.leadingCoeff / x.denom.leadingCoeff with hc
        have hlcd : x.denom.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hden
        have hlcn : x.num.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hnum
        have hcne : c ≠ 0 := div_ne_zero hlcn hlcd
        set w : K[X] := Polynomial.C c * x.denom - x.num with hw
        have hxeq : algebraMap K (RatFunc K) c - x
            = algebraMap K[X] (RatFunc K) w / algebraMap K[X] (RatFunc K) x.denom := by
          have hxd : algebraMap K[X] (RatFunc K) x.num
              = x * algebraMap K[X] (RatFunc K) x.denom :=
            (div_eq_iff hdenne).1 (RatFunc.num_div_denom x)
          have hCc : algebraMap K[X] (RatFunc K) (Polynomial.C c)
              = algebraMap K (RatFunc K) c := by
            rw [RatFunc.algebraMap_eq_C, RatFunc.algebraMap_C]
          rw [eq_div_iff hdenne, hw, map_sub, map_mul, hCc]
          linear_combination hxd
        refine ⟨c, key c ?_⟩
        rcases eq_or_ne w 0 with hw0 | hw0
        · left
          rw [hxeq, hw0]
          simp
        · right
          have hdd : (Polynomial.C c * x.denom).degree = x.num.degree := by
            rw [Polynomial.degree_C_mul hcne, Polynomial.degree_eq_natDegree hden,
              Polynomial.degree_eq_natDegree hnum, heq]
          have hlc : (Polynomial.C c * x.denom).leadingCoeff = x.num.leadingCoeff := by
            rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hc]
            field_simp
          have hdegw : w.degree < x.num.degree := by
            rw [hw, ← hdd]
            exact Polynomial.degree_sub_lt hdd (mul_ne_zero (by simpa using hcne) hden) hlc
          have hdegw' : w.natDegree < x.num.natDegree := by
            have h1 : w.degree = (w.natDegree : WithBot ℕ) :=
              Polynomial.degree_eq_natDegree hw0
            have h2 : x.num.degree = (x.num.natDegree : WithBot ℕ) :=
              Polynomial.degree_eq_natDegree hnum
            rw [h1, h2] at hdegw
            exact_mod_cast hdegw
          have hwne : algebraMap K[X] (RatFunc K) w ≠ 0 := fun hh =>
            hw0 (RatFunc.algebraMap_injective K (hh.trans (map_zero _).symm))
          rw [hxeq]
          simp only [ordZP, ordInfZ, div_eq_mul_inv,
            RatFunc.intDegree_mul hwne (inv_ne_zero hdenne), RatFunc.intDegree_inv,
            RatFunc.intDegree_polynomial]
          omega
  have hiso := (LinearEquiv.ofBijective (constToRes (K := K)) ⟨hinj, hsurj⟩).finrank_eq
  rw [← hiso]
  simp

end P1

end Math2

/-
Multiplicities of monic irreducible polynomials: the local invariants of the projective line.
-/
import Mathlib

namespace Math2

namespace P1

open Polynomial

universe u

variable {K : Type u} [Field K]

/-- A finite place of the projective line over `K`: a monic irreducible polynomial. -/
structure FinPlace (K : Type u) [Field K] where
  /-- The monic irreducible polynomial defining the place. -/
  poly : K[X]
  /-- The polynomial is monic. -/
  monic : poly.Monic
  /-- The polynomial is irreducible. -/
  irred : Irreducible poly

namespace FinPlace

