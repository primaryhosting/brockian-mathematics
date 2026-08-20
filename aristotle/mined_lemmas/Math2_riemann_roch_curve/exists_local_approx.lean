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

lemma exists_local_approx (q : FinPlace K) (x : RatFunc K) :
    ∃ y : RatFunc K, x - y ∈ (projectiveLine K).valSub (some q) 0 ∧
      ∀ r : FinPlace K, r ≠ q → y ∈ (projectiveLine K).valSub (some r) 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by simpa using Submodule.zero_mem _, fun r _ => Submodule.zero_mem _⟩
  set N := x.num with hN
  set D := x.denom with hD
  have hden : D ≠ 0 := RatFunc.denom_ne_zero x
  have hnum : N ≠ 0 := RatFunc.num_ne_zero hx0
  set n := cnt q D with hn
  obtain ⟨b, hb, hqb⟩ := exists_cnt_factor q hden
  have hbne : b ≠ 0 := by
    intro h
    exact hden (by rw [hb, h, mul_zero])
  have hcop : IsCoprime (q.poly ^ n) b := ((q.irred.coprime_iff_not_dvd).2 hqb).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  have hqn : q.poly ^ n ≠ 0 := pow_ne_zero _ q.ne_zero
  have hmapne : ∀ a : K[X], a ≠ 0 → algebraMap K[X] (RatFunc K) a ≠ 0 := fun a ha hh =>
    ha (RatFunc.algebraMap_injective K (hh.trans (map_zero _).symm))
  have hQn := hmapne _ hqn
  have hB := hmapne _ hbne
  have hDne := hmapne _ hden
  have hxd : algebraMap K[X] (RatFunc K) N = x * algebraMap K[X] (RatFunc K) D :=
    (div_eq_iff hDne).1 (RatFunc.num_div_denom x)
  have hDsplit : algebraMap K[X] (RatFunc K) D
      = algebraMap K[X] (RatFunc K) (q.poly ^ n) * algebraMap K[X] (RatFunc K) b := by
    rw [← map_mul, ← hb]
  have huvA : algebraMap K[X] (RatFunc K) u * algebraMap K[X] (RatFunc K) (q.poly ^ n)
      + algebraMap K[X] (RatFunc K) v * algebraMap K[X] (RatFunc K) b = 1 := by
    rw [← map_mul, ← map_mul, ← map_add, huv, map_one]
  refine ⟨algebraMap K[X] (RatFunc K) (N * v) / algebraMap K[X] (RatFunc K) (q.poly ^ n), ?_, ?_⟩
  · have hkey : x - algebraMap K[X] (RatFunc K) (N * v) / algebraMap K[X] (RatFunc K) (q.poly ^ n)
        = algebraMap K[X] (RatFunc K) (N * u) / algebraMap K[X] (RatFunc K) b := by
      rw [div_eq_div_iff hQn hB] at *
      field_simp
      rw [hDsplit] at hxd
      simp only [map_mul]
      linear_combination (algebraMap K[X] (RatFunc K) b) * hxd
        - (algebraMap K[X] (RatFunc K) N) * huvA
    rw [mem_valSub_iff', hkey]
    rcases eq_or_ne (N * u) 0 with h0 | h0
    · exact Or.inl (by rw [h0]; simp)
    · refine Or.inr ?_
      rw [ordZP, ordFinZ_div q h0 hbne, cnt_eq_zero_of_not_dvd q hqb]
      simp
  · intro r hr
    rw [mem_valSub_iff']
    rcases eq_or_ne (N * v) 0 with h0 | h0
    · exact Or.inl (by rw [h0]; simp)
    · refine Or.inr ?_
      rw [ordZP, ordFinZ_div r h0 hqn, cnt_pow_other q r hr]
      simp

/-- Approximation at a finite set of finite places. -/
