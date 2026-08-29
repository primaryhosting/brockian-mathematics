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

lemma denom_eq_one_of_no_poles {f : RatFunc k} (h : ∀ a : k, 0 ≤ ord (some a) f) :
    f.denom = 1 := by
  by_contra hne
  have hdeg : f.denom.degree ≠ 0 := by
    intro h0
    have : f.denom = Polynomial.C (f.denom.coeff 0) := Polynomial.eq_C_of_degree_eq_zero h0
    have hmonic := f.monic_denom
    rw [this] at hmonic ⊢
    simpa [Polynomial.Monic, Polynomial.leadingCoeff] using hmonic
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root f.denom hdeg
  have hda : 1 ≤ f.denom.rootMultiplicity a :=
    (Polynomial.le_rootMultiplicity_iff f.denom_ne_zero).2 (by
      simpa using (Polynomial.dvd_iff_isRoot).2 ha)
  have hna : 1 ≤ f.num.rootMultiplicity a := by
    have := h a
    simp only [ord_some] at this
    omega
  have hnr : f.num.IsRoot a := by
    by_contra hcon
    rw [Polynomial.rootMultiplicity_eq_zero hcon] at hna
    omega
  have hcop := RatFunc.isCoprime_num_denom f
  have hdvd1 : (X - C a) ∣ f.num := (Polynomial.dvd_iff_isRoot).2 hnr
  have hdvd2 : (X - C a) ∣ f.denom := (Polynomial.dvd_iff_isRoot).2 ha
  have := hcop.isUnit_of_dvd' hdvd1 hdvd2
  have hdegXa : (X - C a : k[X]).degree = 1 := Polynomial.degree_X_sub_C a
  have := Polynomial.isUnit_iff_degree_eq_zero.1 this
  rw [hdegXa] at this
  exact absurd this (by decide)

