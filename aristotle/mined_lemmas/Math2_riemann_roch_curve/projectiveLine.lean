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

noncomputable def projectiveLine (K : Type u) [Field K] :
    PreCurve K (RatFunc K) (Place K) where
  ord := ordP
  deg := degP
  ord_algebraMap := by
    intro p c hc
    have hne : algebraMap K (RatFunc K) c ≠ 0 := by
      simp [RatFunc.algebraMap_eq_C, hc]
    refine ordP_eq_zero_of_ordZP_eq_zero hne ?_
    have hpoly : algebraMap K (RatFunc K) c = algebraMap K[X] (RatFunc K) (Polynomial.C c) := by
      rw [RatFunc.algebraMap_eq_C, RatFunc.algebraMap_C]
    cases p with
    | none =>
        simp only [ordZP, hpoly, ordInfZ_algebraMap, Polynomial.natDegree_C]
        simp
    | some q =>
        simp only [ordZP, hpoly, ordFinZ_algebraMap]
        simp [cnt_C q hc]
  uniformizer := by
    intro p
    cases p with
    | none =>
        refine ⟨(RatFunc.X : RatFunc K)⁻¹, ?_⟩
        have hne : (RatFunc.X : RatFunc K)⁻¹ ≠ 0 := inv_ne_zero RatFunc.X_ne_zero
        rw [ordP_of_ne_zero none hne]
        norm_cast
        simp [ordZP, ordInfZ, RatFunc.intDegree_inv]
    | some q =>
        refine ⟨algebraMap K[X] (RatFunc K) q.poly, ?_⟩
        have hne : algebraMap K[X] (RatFunc K) q.poly ≠ 0 := fun hh =>
          q.ne_zero (RatFunc.algebraMap_injective K (hh.trans (map_zero _).symm))
        rw [ordP_of_ne_zero (some q) hne]
        norm_cast
        simp [ordZP, ordFinZ_algebraMap, cnt_self]
  ord_support := ord_support_P1
  degree_principal := by
    intro x hx S hS
    have := degree_principal_P1 x hx S hS
    rw [← this]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ordP_of_ne_zero p hx]
    simp
  constants := constants_P1
  place_nonempty := ⟨none⟩

end P1

end Math2

/-
The valuation of the projective line at the place at infinity.
-/
import RequestProject.P1.OrdFin

namespace Math2

namespace P1

open Polynomial RatFunc

universe u

variable {K : Type u} [Field K]

/-- The order of vanishing at infinity of a rational function. -/
