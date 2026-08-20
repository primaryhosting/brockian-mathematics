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

lemma polyToRes_surjective : Function.Surjective (polyToRes q) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective ((projectiveLine K).maxIdeal (some q)) y
  obtain ⟨x, hx⟩ := x
  rcases eq_or_ne x 0 with rfl | hx0
  · refine ⟨0, ?_⟩
    rw [polyToRes, LinearMap.comp_apply, map_zero]
    rfl
  · have hord : 0 ≤ ordZP (some q) x := by
      rcases (mem_valSub_iff' (some q) 0 x).1 hx with h | h
      · exact absurd h hx0
      · exact h
    have hordfin : (cnt q x.denom : ℤ) ≤ cnt q x.num := by
      simpa [ordZP, ordFinZ] using hord
    have hqden : ¬ q.poly ∣ x.denom := by
      intro hdvd
      have hcd : cnt q x.denom ≠ 0 := fun hc => (cnt_eq_zero_iff q x.denom).1 hc hdvd
      have hcn : cnt q x.num ≠ 0 := by omega
      obtain ⟨u, v, huv⟩ := RatFunc.isCoprime_num_denom x
      have hone : q.poly ∣ (1 : K[X]) := by
        rw [← huv]
        exact dvd_add (Dvd.dvd.mul_left (dvd_of_cnt_ne_zero q hcn) u)
          (Dvd.dvd.mul_left hdvd v)
      exact q.not_isUnit (isUnit_of_dvd_one hone)
    obtain ⟨u, v, huv⟩ := (q.irred.coprime_iff_not_dvd).2 hqden
    refine ⟨x.num * v, ?_⟩
    -- the difference `algebraMap (num * v) - x` lies in the maximal ideal
    have hdenne : algebraMap K[X] (RatFunc K) x.denom ≠ 0 := fun hh =>
      (RatFunc.denom_ne_zero x) (RatFunc.algebraMap_injective K (hh.trans (map_zero _).symm))
    have hkey : algebraMap K[X] (RatFunc K) (x.num * v) - x
        = algebraMap K[X] (RatFunc K) (x.num * (-(u * q.poly)))
          / algebraMap K[X] (RatFunc K) x.denom := by
      have hxd : algebraMap K[X] (RatFunc K) x.num
          = x * algebraMap K[X] (RatFunc K) x.denom :=
        (div_eq_iff hdenne).1 (RatFunc.num_div_denom x)
      have huvA : algebraMap K[X] (RatFunc K) u * algebraMap K[X] (RatFunc K) q.poly
          + algebraMap K[X] (RatFunc K) v * algebraMap K[X] (RatFunc K) x.denom = 1 := by
        rw [← map_mul, ← map_mul, ← map_add, huv, map_one]
      rw [eq_div_iff hdenne]
      simp only [map_mul, map_neg]
      linear_combination hxd + algebraMap K[X] (RatFunc K) x.num * huvA
    rw [polyToRes, LinearMap.comp_apply]
    simp only [Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq, mem_maxIdeal_iff]
    have hcoe : ((polyToLocal q (x.num * v) - ⟨x, hx⟩ :
        ↥((projectiveLine K).valSub (some q) 0)) : RatFunc K)
        = algebraMap K[X] (RatFunc K) (x.num * v) - x := rfl
    rw [hcoe, hkey]
    rcases eq_or_ne (x.num * (-(u * q.poly))) 0 with h0 | h0
    · left
      rw [h0]
      simp
    · right
      rw [ordZP, ordFinZ_div q h0 (RatFunc.denom_ne_zero x)]
      have hnum : x.num ≠ 0 := RatFunc.num_ne_zero hx0
      have huq : (-(u * q.poly)) ≠ 0 := by
        intro h
        exact h0 (by rw [h, mul_zero])
      have hu : u ≠ 0 := by
        intro h
        apply huq
        rw [h, zero_mul, neg_zero]
      rw [cnt_mul q hnum huq]
      have hcq : cnt q (-(u * q.poly)) = cnt q u + 1 := by
        rw [show (-(u * q.poly)) = (-u) * q.poly by ring,
          cnt_mul q (neg_ne_zero.2 hu) q.ne_zero, cnt_self]
        congr 1
        rcases eq_or_ne u 0 with rfl | hu' 
        · simp
        · have h1 : cnt q (-u) = cnt q u := by
            have : (-u : K[X]) = (-1 : K[X]) * u := by ring
            rw [this, cnt_mul q (by simp) hu, cnt_of_isUnit q (isUnit_one.neg)]
            simp
          exact h1
      rw [hcq]
      omega

/-- The residue field at a finite place has dimension the degree of the place. -/
