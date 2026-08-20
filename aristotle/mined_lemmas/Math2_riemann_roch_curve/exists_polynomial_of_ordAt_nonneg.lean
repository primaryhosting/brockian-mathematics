import Mathlib

/-!
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
## Scope and setup

We formalise the Riemann–Roch theorem for the projective line `ℙ¹` over an algebraically
closed field `k`, a smooth projective curve, with everything built from scratch:

* the places of `ℙ¹` are the points `a : k` of the affine line together with the point at
  infinity, and the associated discrete valuations are `ordAt a` and `ordInf`;
* a divisor is a finitely supported family of integers on the affine points together with a
  coefficient at infinity, and `Divisor.deg` is its degree;
* `RRSpace D` is the Riemann-Roch space `L(D) = {f : div f + D ≥ 0}` and
  `ell D = ℓ(D) = dim_k L(D)`;
* `canonicalDivisor k` is the divisor `-2·∞` of the differential `dt`, and the genus is
  defined intrinsically as `genus k = ℓ(K)`.

The main theorem `Math2.riemann_roch_curve` states `ℓ(D) - ℓ(K - D) = deg D + 1 - g`.
It is deduced from the computation `Math2.ell_eq : ℓ(D) = max (deg D + 1) 0`, which is proved
by exhibiting an explicit `k`-linear isomorphism between `L(D)` and the space of polynomials
of degree at most `deg D`.
-/

namespace Math2

open Polynomial

variable {k : Type*} [Field k]

/-! ## Orders of vanishing (the discrete valuations of `ℙ¹`) -/

/-- The order of vanishing at the point `a` of the affine line, of a rational function `f`. -/

theorem exists_polynomial_of_ordAt_nonneg [IsAlgClosed k] {f : RatFunc k}
    (h : ∀ a : k, 0 ≤ ordAt a f) : ∃ u : k[X], f = algebraMap k[X] (RatFunc k) u := by
  have hcop : IsCoprime f.num f.denom := RatFunc.isCoprime_num_denom f
  have hnoroot : ∀ a : k, ¬ f.denom.IsRoot a := by
    intro a ha
    have h1 : 0 < f.denom.rootMultiplicity a :=
      (Polynomial.rootMultiplicity_pos f.denom_ne_zero).2 ha
    have h2 := h a
    simp only [ordAt] at h2
    have h3 : 0 < f.num.rootMultiplicity a := by omega
    have hdvd1 : ((X : k[X]) - C a) ∣ f.num := by
      simpa using pow_dvd_of_le_rootMultiplicity (p := f.num) (a := a) (M := 1) h3
    have hdvd2 : ((X : k[X]) - C a) ∣ f.denom := by
      simpa using pow_dvd_of_le_rootMultiplicity (p := f.denom) (a := a) (M := 1) h1
    have := hcop.isUnit_of_dvd' hdvd1 hdvd2
    exact (Polynomial.not_isUnit_X_sub_C a) this
  have hdeg : f.denom.natDegree = 0 := by
    by_contra hne
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root f.denom
      (fun hd => hne (Polynomial.natDegree_eq_zero_iff_degree_le_zero.2 (le_of_eq hd)))
    exact hnoroot a ha
  have hone : f.denom = 1 := by
    have hm : f.denom.Monic := RatFunc.monic_denom f
    exact hm.natDegree_eq_zero.1 hdeg
  refine ⟨f.num, ?_⟩
  conv_lhs => rw [← RatFunc.num_div_denom f]
  rw [hone, map_one, div_one]

/-! ## Divisors -/

/-- A divisor on `ℙ¹` over `k`: a finitely supported family of integers indexed by the points
of the affine line, together with the coefficient at the point at infinity. -/
abbrev Divisor (k : Type*) [Field k] := (k →₀ ℤ) × ℤ

/-- The degree of a divisor (every point of `ℙ¹` over an algebraically closed field has
degree one). -/
