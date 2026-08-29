import Mathlib

/-!
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Riemann–Roch for the smooth projective curve `ℙ¹`

We develop, from scratch, the divisor theory of the smooth projective curve `ℙ¹` over an
algebraically closed field `k`, whose function field is `RatFunc k`.

* The closed points (places) of `ℙ¹` are the elements of `k` together with the point at
  infinity; this is modelled by `Math2.Place k := Option k` (`none` is the point at infinity).
  Algebraic closedness of `k` is what makes this list of places complete.
* For every place `P` we have the normalized order (valuation) function `Math2.ord P`.
* Divisors are finitely supported `ℤ`-valued functions on places, of degree the sum of their
  coefficients (every closed point of `ℙ¹` over an algebraically closed field has degree one).
* `Math2.LSpace D` is the Riemann–Roch space `L(D) = {f | div f + D ≥ 0} ∪ {0}` and
  `Math2.ell D = ℓ(D)` is its dimension over `k`.
* `Math2.canonical k = -2 ⬝ ∞` is the canonical divisor (the divisor of the differential `dX`)
  and the genus is `g = ℓ(K)`.

The main theorem `Math2.riemann_roch_curve` is `ℓ(D) - ℓ(K - D) = deg D + 1 - g`.
-/

namespace Math2

open Polynomial RatFunc

variable {k : Type*} [Field k]

/-- The closed points of `ℙ¹` over an algebraically closed field `k`: the elements of `k`,
together with the point at infinity `none`. -/
abbrev Place (k : Type*) : Type _ := Option k

/-- The normalized valuation of a rational function at a place of `ℙ¹`:
at a point `a ∈ k` it is the order of vanishing at `a`, at `∞` it is minus the degree. -/

lemma LSpace_single_none (m : ℤ) :
    LSpace (Finsupp.single (none : Place k) m)
      = Submodule.map (polyToRatFunc k) (Polynomial.degreeLT k (m + 1).toNat) := by
  ext f
  constructor
  · rintro (rfl | hf)
    · exact ⟨0, by simp [Polynomial.mem_degreeLT], by simp⟩
    · rcases eq_or_ne f 0 with rfl | h0
      · exact ⟨0, by simp [Polynomial.mem_degreeLT], by simp⟩
      have hpoles : ∀ a : k, 0 ≤ ord (some a) f := by
        intro a
        have := hf (some a)
        simpa using this
      have hden : f.denom = 1 := denom_eq_one_of_no_poles hpoles
      have hfp : f = algebraMap k[X] (RatFunc k) f.num := by
        conv_lhs => rw [← f.num_div_denom]
        rw [hden]
        simp
      have hnum : f.num ≠ 0 := RatFunc.num_ne_zero h0
      have hinf := hf none
      rw [Finsupp.single_eq_same, hfp, ord_algebraMap_none hnum] at hinf
      refine ⟨f.num, ?_, hfp.symm⟩
      rw [Polynomial.mem_degreeLT]
      have hle : (f.num.natDegree : ℤ) ≤ m := by omega
      have : f.num.degree = (f.num.natDegree : ℕ) := Polynomial.degree_eq_natDegree hnum
      rw [this]
      have : (f.num.natDegree : ℤ) < (m + 1).toNat := by omega
      exact_mod_cast Nat.cast_lt.2 (by exact_mod_cast this)
  · rintro ⟨p, hp, rfl⟩
    rcases eq_or_ne p 0 with rfl | hp0
    · exact Or.inl (by simp)
    refine Or.inr fun P => ?_
    rw [Polynomial.mem_degreeLT] at hp
    have hdeg : (p.natDegree : ℤ) ≤ m := by
      have h1 : p.degree = (p.natDegree : ℕ) := Polynomial.degree_eq_natDegree hp0
      rw [h1] at hp
      have : p.natDegree < (m + 1).toNat := by exact_mod_cast hp
      omega
    cases P with
    | none =>
        rw [Finsupp.single_eq_same, polyToRatFunc_apply, ord_algebraMap_none hp0]
        omega
    | some a =>
        rw [polyToRatFunc_apply, ord_algebraMap_some a hp0]
        simp

