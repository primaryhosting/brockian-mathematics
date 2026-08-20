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

lemma constants_P1 (x : RatFunc K) (h : ∀ p : Place K, (0 : WithTop ℤ) ≤ ordP p x) :
    ∃ c : K, algebraMap K (RatFunc K) c = x := by
  classical
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, by simp⟩
  have hden : x.denom = 1 := by
    by_cases hu : IsUnit x.denom
    · exact (RatFunc.monic_denom x).eq_one_of_isUnit hu
    obtain ⟨q, hqm, hqi, hqd⟩ := Polynomial.exists_monic_irreducible_factor x.denom hu
    set r : FinPlace K := ⟨q, hqm, hqi⟩ with hr
    have hcd : cnt r x.denom ≠ 0 := fun hc => (cnt_eq_zero_iff r x.denom).1 hc hqd
    have hge := h (some r)
    rw [ordP_of_ne_zero (some r) hx] at hge
    have hge' : (0 : ℤ) ≤ ordZP (some r) x := by exact_mod_cast hge
    simp only [ordZP, ordFinZ] at hge'
    have hcn : cnt r x.num ≠ 0 := by omega
    have hqn : q ∣ x.num := dvd_of_cnt_ne_zero r hcn
    obtain ⟨u, v, huv⟩ := RatFunc.isCoprime_num_denom x
    have : q ∣ (1 : K[X]) := by
      rw [← huv]
      exact dvd_add (Dvd.dvd.mul_left hqn u) (Dvd.dvd.mul_left hqd v)
    exact absurd (isUnit_of_dvd_one this) hqi.not_isUnit
  have hxpoly : x = algebraMap K[X] (RatFunc K) x.num := by
    conv_lhs => rw [← RatFunc.num_div_denom x]
    rw [hden]
    simp
  have hinf := h none
  rw [ordP_of_ne_zero none hx] at hinf
  have hinf' : (0 : ℤ) ≤ ordZP (none : Place K) x := by exact_mod_cast hinf
  simp only [ordZP, ordInfZ, RatFunc.intDegree, hden, Polynomial.natDegree_one] at hinf'
  have hdeg : x.num.natDegree = 0 := by omega
  refine ⟨x.num.coeff 0, ?_⟩
  rw [RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C, ← Polynomial.eq_C_of_natDegree_eq_zero hdeg,
    ← hxpoly]

/-! ### The projective line as a `PreCurve` -/

/-- The projective line over `K`, as a `PreCurve`. -/
