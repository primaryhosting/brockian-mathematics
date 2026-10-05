/-
# Modularity
Category: Frontier Math
Target: Math2.modularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`, so the required
-- header appears above as a block comment and is repeated as a docstring below.)

import Mathlib

/-!
# Modularity
Category: Frontier Math
Target: Math2.modularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open CongruenceSubgroup

namespace Math2

/-- The number of points of the reduction mod `p` of an integral Weierstrass curve,
counted on the affine model together with the point at infinity. -/

lemma exists_integral_shortModel (E : WeierstrassCurve ℚ) (hE : E.IsElliptic) :
    ∃ (A B : ℤ) (C : WeierstrassCurve.VariableChange ℚ), 4 * A ^ 3 + 27 * B ^ 2 ≠ 0 ∧
      C • ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve ℤ).map (Int.castRingHom ℚ)) = E := by
  haveI : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  haveI : Invertible (3 : ℚ) := invertibleOfNonzero (by norm_num)
  obtain ⟨C₁, hC₁⟩ := E.exists_variableChange_isShortNF
  haveI : (C₁ • E).IsShortNF := hC₁
  -- clear denominators of the short model `C₁ • E`
  have hdne : (C₁ • E).a₄.den * (C₁ • E).a₆.den ≠ 0 :=
    Nat.mul_ne_zero (C₁ • E).a₄.den_nz (C₁ • E).a₆.den_nz
  have hd0 : (((C₁ • E).a₄.den * (C₁ • E).a₆.den : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hdne
  obtain ⟨A, hA⟩ := exists_int_of_den_dvd (C₁ • E).a₄ ((C₁ • E).a₄.den * (C₁ • E).a₆.den) 4
    ⟨(C₁ • E).a₆.den, rfl⟩ (by norm_num)
  obtain ⟨B, hB⟩ := exists_int_of_den_dvd (C₁ • E).a₆ ((C₁ • E).a₄.den * (C₁ • E).a₆.den) 6
    (Dvd.intro_left _ rfl) (by norm_num)
  set C₂ : WeierstrassCurve.VariableChange ℚ :=
    ⟨(Units.mk0 (((C₁ • E).a₄.den * (C₁ • E).a₆.den : ℕ) : ℚ) hd0)⁻¹, 0, 0, 0⟩ with hC₂
  set E₀ : WeierstrassCurve ℤ := ⟨0, 0, 0, A, B⟩ with hE₀
  have hmap : C₂ • (C₁ • E) = E₀.map (Int.castRingHom ℚ) :=
    variableChange_eq_map_int (C₁ • E) _ hd0 A B hA hB
  -- the resulting integral model has non-zero discriminant
  have hΔE : E.Δ ≠ 0 := by
    have h := hE
    rw [WeierstrassCurve.isElliptic_iff] at h
    exact h.ne_zero
  have hΔW : (C₁ • E).Δ ≠ 0 := by
    rw [WeierstrassCurve.variableChange_Δ]
    exact mul_ne_zero (by simp) hΔE
  have hΔ₀ : (E₀.map (Int.castRingHom ℚ)).Δ ≠ 0 := by
    rw [← hmap, WeierstrassCurve.variableChange_Δ]
    refine mul_ne_zero ?_ hΔW
    simp [hC₂]
  have hΔint : E₀.Δ ≠ 0 := by
    intro h
    apply hΔ₀
    rw [WeierstrassCurve.map_Δ, h]
    simp
  have hcomp : (C₂ * C₁) • E = E₀.map (Int.castRingHom ℚ) := by rw [mul_smul, hmap]
  have hAB : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0 := by
    intro h
    exact hΔint (by rw [hE₀, Delta_shortNF, h, mul_zero])
  exact ⟨A, B, (C₂ * C₁)⁻¹, hAB, by rw [← hcomp, inv_smul_smul]⟩

/-- An integral short Weierstrass curve with `4A³ + 27B² ≠ 0` defines an elliptic curve
over `ℚ`. -/
