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

lemma ord_support_finite {f : RatFunc k} (hf : f ≠ 0) :
    (Function.support fun v : Place k => ord v f).Finite := by
  classical
  have hane : f.num * f.denom ≠ 0 :=
    mul_ne_zero (RatFunc.num_ne_zero hf) (RatFunc.denom_ne_zero f)
  have hSfin : {p : FinPlace k | ord (some p) f ≠ 0}.Finite := by
    apply Set.Finite.of_finite_image (f := (Subtype.val : FinPlace k → k[X]))
      _ (Set.injOn_of_injective Subtype.val_injective)
    apply Set.Finite.subset
      ((normalizedFactors (f.num * f.denom)).toFinset : Finset k[X]).finite_toSet
    rintro x ⟨p, hp, rfl⟩
    have hdvd : p.1 ∣ f.num * f.denom := by
      by_contra hnd
      have h1 : ¬ p.1 ∣ f.num := fun h => hnd (h.mul_right _)
      have h2 : ¬ p.1 ∣ f.denom := fun h => hnd (h.mul_left _)
      exact hp (by simp [ord, polOrd, multiplicity_eq_zero.2 h1, multiplicity_eq_zero.2 h2])
    have : p.1 ∈ normalizedFactors (f.num * f.denom) :=
      (mem_normalizedFactors_iff' hane).2 ⟨p.2.2, p.2.1.normalize_eq_self, hdvd⟩
    simpa using this
  apply Set.Finite.subset ((hSfin.image some).insert none)
  rintro (_ | p) hv
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨p, hv, rfl⟩

/-- The principal divisor of a nonzero rational function (and `0` for `f = 0`). -/
