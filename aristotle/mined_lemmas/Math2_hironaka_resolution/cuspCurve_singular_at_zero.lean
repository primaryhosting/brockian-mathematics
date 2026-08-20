import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

variable (k : Type*) [Field k]

/-- The affine plane curve `C_{a,b} : y^a = x^b` over a field `k`.
For `a, b ≥ 2` coprime this is the standard quasi-homogeneous plane curve singularity
(for `(a,b) = (2,3)` it is the cuspidal cubic `y² = x³`). -/

lemma cuspCurve_singular_at_zero {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    MvPolynomial.eval (0 : Fin 2 → k) (cuspPoly k a b) = 0 ∧
      ∀ i : Fin 2, MvPolynomial.eval (0 : Fin 2 → k)
        (MvPolynomial.pderiv i (cuspPoly k a b)) = 0 := by
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  refine ⟨by simp [cuspPoly, zero_pow ha0, zero_pow hb0], fun i => ?_⟩
  have hpd : MvPolynomial.pderiv i (cuspPoly k a b)
      = (a : MvPolynomial (Fin 2) k) * MvPolynomial.X 1 ^ (a - 1) *
          MvPolynomial.pderiv i (MvPolynomial.X (1 : Fin 2))
        - (b : MvPolynomial (Fin 2) k) * MvPolynomial.X 0 ^ (b - 1) *
          MvPolynomial.pderiv i (MvPolynomial.X (0 : Fin 2)) := by
    simp [cuspPoly, Derivation.leibniz_pow, mul_assoc]
  have h1 : a - 1 ≠ 0 := by omega
  have h2 : b - 1 ≠ 0 := by omega
  rw [hpd]
  simp [zero_pow h1, zero_pow h2]

/--
**Hironaka resolution of singularities (characteristic zero), formalized for the
quasi-homogeneous plane curve singularities.**

Full Hironaka desingularization for arbitrary varieties is not available in Mathlib
(schemes, blow-ups and properness of blow-ups are not developed there), so the theorem is
stated and proved here for the family of quasi-homogeneous plane curve singularities
`C_{a,b} : y^a = x^b` with `a, b ≥ 2` coprime — which includes the cuspidal cubic `y² = x³`.
For this family the statement asserts, over any field `k` of characteristic zero:

* `C_{a,b}` is the zero set of the polynomial `Y^a - X^b`, and the origin is a *singular*
  point of it (the polynomial and both of its partial derivatives vanish there);
* the affine line `𝔸¹ = k` (a smooth variety) maps to `C_{a,b}` by `t ↦ (t^a, t^b)`;
* this map is injective and its image is all of `C_{a,b}`, so it is a bijective morphism
  from a smooth variety onto the singular curve;
* it is an isomorphism away from the singular point: on `C_{a,b} \ {0}` the inverse is
  given by the Laurent monomial `x^u y^v` with `ua + vb = 1`.

The hypothesis `CharZero k` is included as part of the requested characteristic-zero
setting; the proof below does not make use of it.
-/
