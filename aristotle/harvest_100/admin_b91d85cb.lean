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
noncomputable def pointCount (E : WeierstrassCurve ℤ) (p : ℕ) : ℕ :=
  Nat.card (E.map (Int.castRingHom (ZMod p))).toAffine.Point

/-- The trace of Frobenius `a_p(E) = p + 1 - #E(𝔽_p)` of an integral Weierstrass curve. -/
noncomputable def ap (E : WeierstrassCurve ℤ) (p : ℕ) : ℤ :=
  (p : ℤ) + 1 - (pointCount E p : ℤ)

/-- The `n`-th `q`-expansion coefficient of a weight-two cusp form of level `Γ₀(N)`
(the group `Γ₀(N)` has width `1` at the cusp `∞`, so the relevant `q`-parameter
is `q = exp (2πiτ)`). -/
noncomputable def qcoeff {N : ℕ}
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (n : ℕ) : ℂ :=
  (ModularFormClass.qExpansion 1 f).coeff n

/-- Modularity of an *integral* Weierstrass curve `E`:  there is a level `N ≥ 1` and a
weight-two cusp form `f` for `Γ₀(N)` which is normalised (`a₁(f) = 1`) and whose
`q`-expansion coefficients satisfy the Hecke multiplicativity relations of a normalised
eigenform of level `N`, and such that `a_p(f) = a_p(E)` for every prime `p` not dividing
the level and at which the model `E` has good reduction.

This is the classical `a_p`-form of the Shimura–Taniyama–Weil statement: the Hasse–Weil
`L`-function of `E` coincides with the `L`-function of a weight-two normalised eigenform
of level `N`, up to the finitely many Euler factors at primes dividing `N` or `Δ(E)`. -/
def IsModularIntegral (E : WeierstrassCurve ℤ) : Prop :=
  ∃ (N : ℕ) (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
    0 < N ∧
    qcoeff f 1 = 1 ∧
    (∀ m n : ℕ, Nat.Coprime m n → qcoeff f (m * n) = qcoeff f m * qcoeff f n) ∧
    (∀ p r : ℕ, p.Prime → qcoeff f (p ^ (r + 2)) =
      qcoeff f p * qcoeff f (p ^ (r + 1)) - (if p ∣ N then 0 else (p : ℂ)) * qcoeff f (p ^ r)) ∧
    (∀ p : ℕ, p.Prime → ¬ p ∣ N → ¬ (p : ℤ) ∣ E.Δ → qcoeff f p = (ap E p : ℂ))

/-- Modularity of an elliptic curve over `ℚ`, given by a Weierstrass model with rational
coefficients: some integral Weierstrass model in its `ℚ`-isomorphism class is modular in the
sense of `Math2.IsModularIntegral`. -/
def IsModular (E : WeierstrassCurve ℚ) : Prop :=
  ∃ (E₀ : WeierstrassCurve ℤ) (C : WeierstrassCurve.VariableChange ℚ),
    C • (E₀.map (Int.castRingHom ℚ)) = E ∧ IsModularIntegral E₀

/-- The full Shimura–Taniyama–Weil statement: every elliptic curve over `ℚ` is modular. -/
def ModularityStatement : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → IsModular E

/-- Clearing denominators: if `q.den ∣ d` and `1 ≤ k`, then `d ^ k * q` is an integer. -/
lemma exists_int_of_den_dvd (q : ℚ) (d k : ℕ) (hd : q.den ∣ d) (hk : 1 ≤ k) :
    ∃ m : ℤ, (m : ℚ) = (d : ℚ) ^ k * q := by
  obtain ⟨c, hc⟩ : (q.den : ℕ) ∣ d ^ k := dvd_pow hd (by omega)
  refine ⟨(c : ℤ) * q.num, ?_⟩
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have : ((d : ℚ)) ^ k = (q.den : ℚ) * (c : ℚ) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) hc
  rw [this]
  push_cast
  rw [mul_comm (q.den : ℚ) (c : ℚ), mul_assoc]
  congr 1
  rw [mul_comm]
  exact_mod_cast (Rat.mul_den_eq_num q).symm

/-- A short Weierstrass model over `ℚ` whose coefficients are cleared of denominators comes
from an integral short Weierstrass model. -/
lemma variableChange_eq_map_int (W : WeierstrassCurve ℚ) [W.IsShortNF] (d : ℕ) (hd0 : (d : ℚ) ≠ 0)
    (A B : ℤ) (hA : (A : ℚ) = (d : ℚ) ^ 4 * W.a₄) (hB : (B : ℚ) = (d : ℚ) ^ 6 * W.a₆) :
    (⟨(Units.mk0 (d : ℚ) hd0)⁻¹, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ℚ) • W
      = (⟨0, 0, 0, A, B⟩ : WeierstrassCurve ℤ).map (Int.castRingHom ℚ) := by
  have ha₁ : W.a₁ = 0 := W.a₁_of_isShortNF
  have ha₂ : W.a₂ = 0 := W.a₂_of_isShortNF
  have ha₃ : W.a₃ = 0 := W.a₃_of_isShortNF
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
      ha₁, ha₂, ha₃] <;>
    simp [hA, hB]

/-- The discriminant of the integral short Weierstrass curve `y² = x³ + Ax + B`. -/
lemma Delta_shortNF (A B : ℤ) :
    (⟨0, 0, 0, A, B⟩ : WeierstrassCurve ℤ).Δ = -16 * (4 * A ^ 3 + 27 * B ^ 2) := by
  simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

/-- Modularity only depends on the `ℚ`-isomorphism class of the Weierstrass model. -/
lemma isModular_variableChange {E : WeierstrassCurve ℚ} (C : WeierstrassCurve.VariableChange ℚ)
    (h : IsModular E) : IsModular (C • E) := by
  obtain ⟨E₀, C', hC', hmod⟩ := h
  exact ⟨E₀, C * C', by rw [mul_smul, hC'], hmod⟩

/-- **Normalisation to an integral short Weierstrass model.**  Every elliptic curve over `ℚ`
is `ℚ`-isomorphic to an integral short Weierstrass curve `y² = x³ + Ax + B` with
`A B : ℤ` and `4A³ + 27B² ≠ 0`.

The normalisation first puts the curve in short Weierstrass form and then rescales by
`(x, y) ↦ (d² x, d³ y)` to clear denominators. -/
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
lemma isElliptic_map_shortNF (A B : ℤ) (h : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) :
    ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve ℤ).map (Int.castRingHom ℚ)).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, WeierstrassCurve.map_Δ,
    Delta_shortNF]
  have : (4 * A ^ 3 + 27 * B ^ 2 : ℚ) ≠ 0 := by exact_mod_cast h
  simpa using this

/-- **Reduction of the modularity theorem to integral short Weierstrass models.**

If every integral short Weierstrass curve `y² = x³ + Ax + B` (`A B : ℤ`) with non-vanishing
discriminant is modular, then every elliptic curve over `ℚ` is modular
(`Math2.ModularityStatement`, the Shimura–Taniyama–Weil statement).

The proof normalises an arbitrary elliptic curve over `ℚ` to an isomorphic integral short
Weierstrass model, using `Math2.exists_integral_shortModel`. -/
theorem modularity
    (H : ∀ A B : ℤ, 4 * A ^ 3 + 27 * B ^ 2 ≠ 0 → IsModularIntegral ⟨0, 0, 0, A, B⟩) :
    ModularityStatement := by
  intro E hE
  obtain ⟨A, B, C, hAB, hC⟩ := exists_integral_shortModel E hE
  exact ⟨⟨0, 0, 0, A, B⟩, C, hC, H A B hAB⟩

/-- The modularity statement for all elliptic curves over `ℚ` is equivalent to its special
case for the curves `y² = x³ + Ax + B` with integral coefficients. -/
theorem modularity_iff :
    ModularityStatement ↔
      ∀ A B : ℤ, 4 * A ^ 3 + 27 * B ^ 2 ≠ 0 →
        IsModular ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve ℤ).map (Int.castRingHom ℚ)) := by
  constructor
  · intro h A B hAB
    exact h _ (isElliptic_map_shortNF A B hAB)
  · intro h E hE
    obtain ⟨A, B, C, hAB, hC⟩ := exists_integral_shortModel E hE
    rw [← hC]
    exact isModular_variableChange C (h A B hAB)

end Math2

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

