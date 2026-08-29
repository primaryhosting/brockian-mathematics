/-
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module doc-comment `/-! ... -/` before `import`, so the header
-- above is a plain block comment; it is repeated verbatim as a module docstring below.)

import Mathlib

/-!
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial UniqueFactorizationMonoid

namespace Math2

/-!
## The Riemann–Roch theorem, cohomological form

`CurveData Point` bundles the standard cohomological data of a smooth projective curve
whose closed points are indexed by `Point`:

* `ptDeg P` is the degree of the closed point `P`;
* `h0 D` and `h1 D` are `dim H⁰(X, 𝒪(D))` and `dim H¹(X, 𝒪(D))`;
* `canonical` is a canonical divisor `K` and `genus` is the genus `g = dim H¹(X, 𝒪)`;
* `chi_step` is additivity of the Euler characteristic along the exact sequence
  `0 → 𝒪(D) → 𝒪(D+P) → k(P) → 0`;
* `serre_duality` is Serre duality `H¹(D)^∨ ≅ H⁰(K - D)`.
-/

/-- Cohomological data of divisors on a smooth projective curve. -/
structure CurveData (Point : Type*) where
  /-- The degree of a closed point. -/
  ptDeg : Point → ℤ
  /-- `h0 D = dim H⁰(X, 𝒪(D)) = ℓ(D)`. -/
  h0 : (Point →₀ ℤ) → ℤ
  /-- `h1 D = dim H¹(X, 𝒪(D))`. -/
  h1 : (Point →₀ ℤ) → ℤ
  /-- A canonical divisor of the curve. -/
  canonical : Point →₀ ℤ
  /-- The genus of the curve. -/
  genus : ℤ
  /-- `ℓ(0) = 1`: the global regular functions are the constants. -/
  h0_zero : h0 0 = 1
  /-- `dim H¹(X, 𝒪) = g`. -/
  h1_zero : h1 0 = genus
  /-- Additivity of the Euler characteristic along `0 → 𝒪(D) → 𝒪(D+P) → k(P) → 0`. -/
  chi_step : ∀ (D : Point →₀ ℤ) (P : Point),
    h0 (D + Finsupp.single P 1) - h1 (D + Finsupp.single P 1) = (h0 D - h1 D) + ptDeg P
  /-- Serre duality. -/
  serre_duality : ∀ D, h1 D = h0 (canonical - D)

namespace CurveData

variable {Point : Type*} (C : CurveData Point)

/-- The degree of a divisor. -/

lemma isPoly_iff {f : RatFunc k} (hf : f ≠ 0) :
    (∀ q : MonicIrr k, 0 ≤ ord (some q) f) ↔ ∃ g : k[X], f = algebraMap k[X] (RatFunc k) g := by
  constructor
  · intro h
    have hden : f.denom = 1 := by
      by_contra hne
      have hdu : ¬ IsUnit f.denom := fun hu => hne (f.monic_denom.eq_one_of_isUnit hu)
      obtain ⟨p, hp⟩ := exists_monicIrr_dvd (RatFunc.denom_ne_zero f) hdu
      have h1 : 1 ≤ cnt p f.denom := one_le_cnt_of_dvd p hp
      have h2 : cnt p f.num = 0 := by
        refine cnt_eq_zero_of_not_dvd p fun hdvd => ?_
        exact p.2.2.not_isUnit ((RatFunc.isCoprime_num_denom f).isUnit_of_dvd' hdvd hp)
      have := h p
      simp only [ord, h2] at this
      linarith
    refine ⟨f.num, ?_⟩
    have := RatFunc.num_div_denom f
    rw [hden] at this
    simpa using this.symm
  · rintro ⟨g, rfl⟩ q
    simp only [ord, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, cnt_one, sub_zero]
    exact cnt_nonneg q g

/-! ### Spaces of polynomials of bounded degree -/

variable (k) in
/-- Polynomials of degree at most `m` (the zero submodule when `m < 0`). -/
