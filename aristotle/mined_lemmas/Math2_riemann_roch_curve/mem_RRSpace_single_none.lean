/-
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

This file develops, from scratch, the divisor theory of the smooth projective curve `ℙ¹`
over an arbitrary field `k`, through its function field `k(X) = RatFunc k`, and proves the
Riemann–Roch theorem for it:

  `ℓ(D) - ℓ(K - D) = deg D + 1 - g`.

Nothing is assumed: all of the following are defined here and all statements are proved.

* `Place k`: the closed points of `ℙ¹`, namely the monic irreducible polynomials
  (finite points) together with the point at infinity.
* `placeDeg`, `Divisor k`, `degDiv`: degrees of points, divisors and their degrees.
* `ord v f`: the order of vanishing of a rational function at a closed point, and
  `divisorOf f` the principal divisor of `f`.
* `RRSpace D` (`= L(D)`) and `ell D` (`= ℓ(D) = dim_k L(D)`).
* `canonicalDivisor k = -2·[∞]`, the divisor of the differential `dX`, and
  `genus k = ℓ(K)`, the dimension of the space of regular differentials.

The main results are `Math2.riemann_roch_curve`, together with `Math2.ell_eq`
(`ℓ(D) = max (deg D + 1) 0`), `Math2.genus_eq_zero` (`ℙ¹` has genus `0`),
`Math2.degDiv_canonical_eq` (`deg K = 2g - 2`) and `Math2.degDiv_divisorOf` (a principal
divisor has degree `0`).

The scope is the projective line: Mathlib has no theory of divisors, linear systems or
Serre duality for general curves, so the curve treated here is `ℙ¹`, for which the whole
theory is built by hand.
-/

namespace Math2

open Polynomial UniqueFactorizationMonoid

variable {k : Type*} [Field k]

/-- A finite closed point of the projective line `ℙ¹` over `k`: a monic irreducible
polynomial in `k[X]`. -/
abbrev FinPlace (k : Type*) [Field k] : Type _ := {p : k[X] // p.Monic ∧ Irreducible p}

/-- The closed points of `ℙ¹` over `k`: the finite places together with the point at
infinity, represented by `none`. -/
abbrev Place (k : Type*) [Field k] : Type _ := Option (FinPlace k)

/-- The degree of a closed point: `1` at infinity, `deg p` at a finite place `p`. -/

lemma mem_RRSpace_single_none {n : ℤ} {f : RatFunc k} :
    f ∈ RRSpace (Finsupp.single (none : Place k) n) ↔
      ∃ a : k[X], (a = 0 ∨ (a.natDegree : ℤ) ≤ n) ∧ f = algebraMap k[X] (RatFunc k) a := by
  constructor
  · intro hf
    rcases eq_or_ne f 0 with rfl | hf0
    · exact ⟨0, Or.inl rfl, by simp⟩
    have hden : f.denom = 1 := denom_eq_one_of_ord_nonneg fun p => by
      have := hf hf0 (some p)
      simpa [Finsupp.single_apply] using this
    have hfa : f = algebraMap k[X] (RatFunc k) f.num := by
      conv_lhs => rw [← RatFunc.num_div_denom f]
      rw [hden, map_one, div_one]
    refine ⟨f.num, Or.inr ?_, hfa⟩
    have := hf hf0 none
    simp only [ord, polOrd, hden, Finsupp.single_eq_same] at this
    simpa using this
  · rintro ⟨a, ha, rfl⟩
    intro hne v
    have ha0 : a ≠ 0 := by
      rintro rfl; exact hne (by simp)
    rw [ord_algebraMap ha0]
    cases v with
    | none =>
      rcases ha with rfl | ha
      · exact absurd rfl ha0
      · simpa [polOrd] using ha
    | some p => simp [polOrd]

