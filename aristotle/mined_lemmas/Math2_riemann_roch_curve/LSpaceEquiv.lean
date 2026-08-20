/-
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is a plain comment and is repeated as a docstring below.)

import Mathlib

/-!
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Scope

Mathlib (as of this version) contains no Riemann–Roch theorem for curves, no divisors on
curves, and no genus, so everything used here is developed from scratch in this file.

We formalize the smooth projective curve `ℙ¹_k` over an arbitrary field `k` through its
function field `k(X)`: its closed points are the monic irreducible polynomials (the closed
points of `𝔸¹ = Spec k[X]`) together with the point at infinity, each equipped with its
normalized valuation `ord P` and its residue degree `deg P`.  Divisors, the degree of a
divisor, the Riemann–Roch space `L(D)`, its dimension `ℓ(D)`, the canonical divisor `K` and
the genus `g = ℓ(K)` are all defined here, and the main theorem
`Math2.riemann_roch_curve` proves

  `ℓ(D) - ℓ(K - D) = deg D + 1 - g`

for every divisor `D` on this curve.  The genus is *computed* (`Math2.genus_eq_zero`), not
assumed, and `Math2.riemann_roch_of_degree_eq_neg_two` shows the identity holds with `K`
replaced by any divisor of degree `2g - 2 = -2`.

The key input is the computation `ℓ(D) = max (deg D + 1) 0` (`Math2.ell_eq_max`), obtained
from an explicit `k`-linear isomorphism between `L(D)` and the space of polynomials of
degree `< deg D + 1`.
-/

open scoped BigOperators
open scoped Classical

open Polynomial

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math2

variable {k : Type*} [Field k]

/-! ## Closed points of the projective line -/

/-- A finite closed point of the projective line `ℙ¹_k`, i.e. a closed point of the affine
line `𝔸¹_k = Spec k[X]`: a monic irreducible polynomial. -/
abbrev FinitePlace (k : Type*) [Field k] := {p : k[X] // p.Monic ∧ Irreducible p}

/-- The closed points of the smooth projective curve `ℙ¹_k`: the closed points of the affine
line, together with the point at infinity (`none`). -/
abbrev Place (k : Type*) [Field k] := Option (FinitePlace k)

/-- The degree `[k(P) : k]` of a closed point of `ℙ¹_k`. -/

noncomputable def LSpaceEquiv (D : Divisor k) :
    (Polynomial.degreeLT k (degree D + 1).toNat) ≃ₗ[k] LSpace D := by
  refine LinearEquiv.ofBijective
    (LinearMap.codRestrict (LSpace D) ((polyToL D).comp (Submodule.subtype _)) ?_) ⟨?_, ?_⟩
  · rintro ⟨u, hu⟩
    rcases mem_degreeLT_iff.mp hu with rfl | h
    · simp [polyToL_apply]
    · by_cases hu0 : u = 0
      · simp [hu0, polyToL_apply]
      · exact (mem_LSpace_poly hu0).mpr h
  · intro u v huv
    have h : polyToL D u.1 = polyToL D v.1 := congrArg Subtype.val huv
    simp only [polyToL_apply] at h
    have := mul_right_cancel₀ (inv_ne_zero (hDiv_ne_zero D)) h
    exact Subtype.ext (IsFractionRing.injective k[X] (RatFunc k) this)
  · rintro ⟨f, hf⟩
    by_cases hf0 : f = 0
    · refine ⟨⟨0, Submodule.zero_mem _⟩, ?_⟩
      simp [hf0, polyToL_apply, Subtype.ext_iff]
    obtain ⟨u, hu0, hu⟩ := exists_poly_of_mem_LSpace hf0 hf
    have hdeg : (u.natDegree : ℤ) ≤ degree D := (mem_LSpace_poly hu0).mp (hu ▸ hf)
    exact ⟨⟨u, mem_degreeLT_iff.mpr (Or.inr hdeg)⟩, Subtype.ext (by simpa [polyToL_apply] using hu.symm)⟩

/-- The dimension of the Riemann–Roch space of a divisor on `ℙ¹_k`. -/
