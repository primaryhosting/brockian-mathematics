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

lemma exists_poly_approx_inf (z : RatFunc K) :
    ∃ g : K[X], z - algebraMap K[X] (RatFunc K) g
      ∈ (projectiveLine K).valSub (none : Place K) 0 := by
  set g : K[X] := z.num /ₘ z.denom with hg
  set r : K[X] := z.num %ₘ z.denom with hrdef
  have hmon : z.denom.Monic := RatFunc.monic_denom z
  have hden : z.denom ≠ 0 := RatFunc.denom_ne_zero z
  have hmapne : ∀ a : K[X], a ≠ 0 → algebraMap K[X] (RatFunc K) a ≠ 0 := fun a ha hh =>
    ha (RatFunc.algebraMap_injective K (hh.trans (map_zero _).symm))
  have hDne := hmapne _ hden
  have hxd : algebraMap K[X] (RatFunc K) z.num = z * algebraMap K[X] (RatFunc K) z.denom :=
    (div_eq_iff hDne).1 (RatFunc.num_div_denom z)
  have hsum : r + z.denom * g = z.num := Polynomial.modByMonic_add_div z.num hmon
  have hr : r = z.num - z.denom * g := by linear_combination hsum
  have hkey : z - algebraMap K[X] (RatFunc K) g
      = algebraMap K[X] (RatFunc K) r / algebraMap K[X] (RatFunc K) z.denom := by
    rw [eq_div_iff hDne, hr, map_sub, map_mul]
    linear_combination hxd
  refine ⟨g, ?_⟩
  rw [mem_valSub_iff', hkey]
  rcases eq_or_ne r 0 with h0 | h0
  · exact Or.inl (by rw [h0]; simp)
  · refine Or.inr ?_
    have hdeg : r.natDegree < z.denom.natDegree := by
      have h1 := Polynomial.degree_modByMonic_lt z.num hmon
      rw [← hrdef, Polynomial.degree_eq_natDegree h0,
        Polynomial.degree_eq_natDegree hden] at h1
      exact_mod_cast h1
    have hrne := hmapne _ h0
    simp only [ordZP, ordInfZ, div_eq_mul_inv,
      RatFunc.intDegree_mul hrne (inv_ne_zero hDne), RatFunc.intDegree_inv,
      RatFunc.intDegree_polynomial]
    omega

/-- **Strong approximation** for the projective line: the everywhere-integral adeles
together with the rational functions span the whole adele space. -/
