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

lemma sum_natDegree_cnt (a : K[X]) (ha : a ≠ 0) (S : Finset (FinPlace K))
    (hS : ∀ q : FinPlace K, q ∉ S → cnt q a = 0) :
    ∑ q ∈ S, (q.poly.natDegree : ℤ) * (cnt q a : ℤ) = (a.natDegree : ℤ) := by
  classical
  induction a using UniqueFactorizationMonoid.induction_on_prime generalizing S with
  | h₁ => exact absurd rfl ha
  | h₂ u hu =>
      have hzero : ∀ q ∈ S, ((q.poly.natDegree : ℤ) * (cnt q u : ℤ)) = 0 := by
        intro q _
        rw [cnt_of_isUnit q hu]
        simp
      rw [Finset.sum_congr rfl hzero]
      simp [Polynomial.natDegree_eq_zero_of_isUnit hu]
  | h₃ b p hb hp ih =>
      have hpne : p ≠ 0 := hp.ne_zero
      have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hpne
      have hunit : IsUnit (Polynomial.C (p.leadingCoeff⁻¹) : K[X]) :=
        isUnit_C.2 (Ne.isUnit (inv_ne_zero hlc))
      have hassoc0 : Associated p (p * Polynomial.C (p.leadingCoeff⁻¹)) :=
        (associated_mul_isUnit_right_iff hunit).2 (Associated.refl p)
      set q₀ : FinPlace K := ⟨p * Polynomial.C (p.leadingCoeff⁻¹), monic_mul_leadingCoeff_inv hpne,
        hassoc0.irreducible hp.irreducible⟩ with hq₀
      have hp_eq : p = q₀.poly * Polynomial.C p.leadingCoeff := by
        rw [hq₀]
        show p = p * Polynomial.C (p.leadingCoeff⁻¹) * Polynomial.C p.leadingCoeff
        rw [mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hlc, Polynomial.C_1, mul_one]
      have hcntp : ∀ r : FinPlace K, cnt r p = if r = q₀ then 1 else 0 := by
        intro r
        rw [hp_eq, cnt_mul r q₀.ne_zero (by simpa using hlc), cnt_C r hlc, add_zero]
        by_cases hr : r = q₀
        · rw [if_pos hr, hr, cnt_self]
        · rw [if_neg hr, cnt_other r q₀ hr]
      have hcnt : ∀ r : FinPlace K, cnt r (p * b) = cnt r p + cnt r b := fun r =>
        cnt_mul r hpne hb
      have hSb : ∀ r : FinPlace K, r ∉ S → cnt r b = 0 := by
        intro r hr
        have h := hS r hr
        rw [hcnt r] at h
        omega
      have hq₀S : q₀ ∈ S := by
        by_contra h
        have h2 := hS q₀ h
        rw [hcnt, hcntp q₀, if_pos rfl] at h2
        omega
      have hsum : ∑ r ∈ S, (r.poly.natDegree : ℤ) * (cnt r (p * b) : ℤ)
          = (∑ r ∈ S, (r.poly.natDegree : ℤ) * (cnt r p : ℤ))
            + ∑ r ∈ S, (r.poly.natDegree : ℤ) * (cnt r b : ℤ) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hcnt r]
        push_cast
        ring
      have h1 : ∑ r ∈ S, (r.poly.natDegree : ℤ) * (cnt r p : ℤ) = (q₀.poly.natDegree : ℤ) := by
        rw [Finset.sum_eq_single q₀]
        · rw [hcntp q₀, if_pos rfl]
          simp
        · intro r _ hr
          rw [hcntp r, if_neg hr]
          simp
        · intro h
          exact absurd hq₀S h
      have h2 := ih hb S hSb
      have hdeg : q₀.poly.natDegree = p.natDegree := by
        rw [hq₀]
        show (p * Polynomial.C (p.leadingCoeff⁻¹)).natDegree = p.natDegree
        rw [Polynomial.natDegree_mul_C (inv_ne_zero hlc)]
      rw [hsum, h1, h2, Polynomial.natDegree_mul hpne hb, hdeg]
      push_cast
      ring

/-! ### Supports -/

/-- A finite set of finite places containing all zeros and poles of a nonzero rational
function. -/
