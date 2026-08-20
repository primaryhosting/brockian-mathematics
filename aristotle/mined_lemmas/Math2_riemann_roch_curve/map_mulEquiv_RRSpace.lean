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

theorem map_mulEquiv_RRSpace [IsAlgClosed k] (D : Divisor k) :
    Submodule.map (mulEquiv (divisorFun D) (divisorFun_ne_zero D)).toLinearMap (RRSpace D)
      = polySpace k (D.deg + 1).toNat := by
  classical
  set H := divisorFun D with hHdef
  have hH : H ≠ 0 := divisorFun_ne_zero D
  set S : ℤ := D.1.sum (fun _ n => n) with hS
  have hdeg : D.deg = S + D.2 := rfl
  have hordH : ∀ a : k, ordAt a H = D.1 a := ordAt_divisorFun D
  have hoinfH : ordInf H = -S := ordInf_divisorFun D
  ext g
  constructor
  · rintro ⟨f, hf, rfl⟩
    have hgf : (mulEquiv H hH).toLinearMap f = f * H := rfl
    rw [hgf]
    rcases hf with rfl | ⟨hf1, hf2⟩
    · simp
    by_cases hf0 : f = 0
    · simp [hf0]
    have hfH : f * H ≠ 0 := mul_ne_zero hf0 hH
    have hordmul : ∀ a : k, ordAt a (f * H) = ordAt a f + D.1 a := by
      intro a
      rw [ordAt_mul a hf0 hH, hordH a]
    obtain ⟨u, hu⟩ := exists_polynomial_of_ordAt_nonneg (f := f * H) (by
      intro a
      have := hf1 a
      rw [hordmul a]
      omega)
    have hu0 : u ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hu
      exact hfH hu
    have hoinf : ordInf (f * H) = ordInf f - S := by
      rw [ordInf_mul hf0 hH, hoinfH]
      ring
    have hdegu : (u.natDegree : ℤ) ≤ D.deg := by
      have h1 : ordInf (algebraMap k[X] (RatFunc k) u) = -(u.natDegree : ℤ) :=
        ordInf_polynomial u
      rw [← hu, hoinf] at h1
      omega
    refine mem_polySpace_iff.2 ⟨u, ?_, hu⟩
    refine (Polynomial.natDegree_lt_iff_degree_lt hu0).1 ?_
    have : (0 : ℤ) ≤ (u.natDegree : ℤ) := Int.natCast_nonneg _
    omega
  · intro hg
    obtain ⟨u, hudeg, rfl⟩ := mem_polySpace_iff.1 hg
    refine ⟨algebraMap k[X] (RatFunc k) u * H⁻¹, ?_, ?_⟩
    · rcases eq_or_ne u 0 with rfl | hu0
      · simp
      have hne : algebraMap k[X] (RatFunc k) u ≠ 0 := RatFunc.algebraMap_ne_zero hu0
      have hinvne : H⁻¹ ≠ 0 := inv_ne_zero hH
      have hordu : ∀ a : k, ordAt a (algebraMap k[X] (RatFunc k) u * H⁻¹)
          = (u.rootMultiplicity a : ℤ) - D.1 a := by
        intro a
        rw [ordAt_mul a hne hinvne, ordAt_inv, ordAt_polynomial, hordH a]
        ring
      have hoinfu : ordInf (algebraMap k[X] (RatFunc k) u * H⁻¹) = -(u.natDegree : ℤ) + S := by
        rw [ordInf_mul hne hinvne, ordInf_inv, hoinfH, ordInf_polynomial]
        ring
      have hnd : u.natDegree < (D.deg + 1).toNat :=
        (Polynomial.natDegree_lt_iff_degree_lt hu0).2 hudeg
      refine Or.inr ⟨fun a => ?_, ?_⟩
      · rw [hordu a]
        have : (0 : ℤ) ≤ (u.rootMultiplicity a : ℤ) := Int.natCast_nonneg _
        omega
      · rw [hoinfu]
        have h2 : (u.natDegree : ℤ) < ((D.deg + 1).toNat : ℤ) := by exact_mod_cast hnd
        omega
    · show algebraMap k[X] (RatFunc k) u * H⁻¹ * H = algebraMap k[X] (RatFunc k) u
      field_simp

/-- `ℓ(D) = max (deg D + 1) 0`. -/
