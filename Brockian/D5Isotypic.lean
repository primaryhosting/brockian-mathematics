/-
  Brockian/D5Isotypic.lean — cyclic Fourier modes on the D₅ vertex representation.

  ## Proved

  * Rotation pullback identity and composition.
  * Primitive fifth root `ω` and additive power map on `Fin 5`.
  * Eigenmodes `vⱼ` and rotation eigenrelation.
  * Character sums; non-constant modes are zero-sum.
  * Cyclic projector diagonalizes eigenmodes.

  ## Not claimed: full D₅ real-irrep decomposition; RH.

  AXLE @ lean-4.32.0; axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.D5Representation
import Brockian.Automorphism

open BigOperators Complex DihedralGroup
open Brockian.D5Representation Brockian.Automorphism

namespace Brockian.D5Isotypic

/-! ### Rotation pullback -/

theorem rotIso_symm_apply (k x : Fin 5) : (rotIso k).symm x = x - k := by
  -- From `apply_symm_apply`: `(rotIso k).symm x + k = x`, hence the claim.
  have hx : (rotIso k).symm x + k = x := by
    simpa only [rotIso_apply] using (rotIso k).apply_symm_apply x
  exact eq_sub_of_add_eq hx

theorem d5Pull_r_apply (k : Fin 5) (f : VertexSpace) (x : Fin 5) :
    d5Pull (r (k : ZMod 5)) f x = f (x - k) := by
  simp only [d5Pull_apply, dihedralHom_r]
  change f ((rotIso k).symm x) = f (x - k)
  rw [rotIso_symm_apply]

theorem d5Pull_r_one_apply (f : VertexSpace) (x : Fin 5) :
    d5Pull (r (1 : ZMod 5)) f x = f (x - 1) :=
  d5Pull_r_apply 1 f x

theorem d5Pull_r_mul (a b : Fin 5) (f : VertexSpace) :
    d5Pull (r (a : ZMod 5)) (d5Pull (r (b : ZMod 5)) f) =
      d5Pull (r ((a + b : Fin 5) : ZMod 5)) f := by
  ext x
  simp only [d5Pull_r_apply, sub_sub, add_comm b a]

/-! ### Fifth root -/

noncomputable def omega : ℂ := exp (2 * Real.pi * I / 5)

local notation "ω" => omega

theorem omega_isPrimitiveRoot : IsPrimitiveRoot ω 5 :=
  isPrimitiveRoot_exp 5 (by decide)

theorem omega_pow_five : ω ^ 5 = 1 :=
  omega_isPrimitiveRoot.pow_eq_one

theorem orderOf_omega : orderOf ω = 5 :=
  omega_isPrimitiveRoot.eq_orderOf.symm

noncomputable def omegaPow (a : Fin 5) : ℂ := ω ^ a.val

@[simp] theorem omegaPow_zero : omegaPow 0 = 1 := by simp [omegaPow]

@[simp] theorem omegaPow_one : omegaPow 1 = ω := by simp [omegaPow]

theorem omega_pow_modEq {m n : ℕ} (h : m ≡ n [MOD 5]) : ω ^ m = ω ^ n := by
  have hord : orderOf ω = 5 := orderOf_omega
  calc ω ^ m = ω ^ (m % orderOf ω) := (pow_mod_orderOf (x := ω) (n := m)).symm
    _ = ω ^ (m % 5) := by rw [hord]
    _ = ω ^ (n % 5) := by
        have : m % 5 = n % 5 := h
        rw [this]
    _ = ω ^ (n % orderOf ω) := by rw [hord]
    _ = ω ^ n := pow_mod_orderOf (x := ω) (n := n)

theorem omegaPow_add (a b : Fin 5) : omegaPow (a + b) = omegaPow a * omegaPow b := by
  simp only [omegaPow, Fin.val_add]
  have hmod : ω ^ ((a.val + b.val) % 5) = ω ^ (a.val + b.val) :=
    omega_pow_modEq (Nat.mod_modEq (a.val + b.val) 5)
  rw [hmod, pow_add]

theorem omegaPow_neg (a : Fin 5) : omegaPow (-a) = (omegaPow a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← omegaPow_add, neg_add_cancel, omegaPow_zero]

theorem omegaPow_sub (a b : Fin 5) : omegaPow (a - b) = omegaPow a * (omegaPow b)⁻¹ := by
  rw [sub_eq_add_neg, omegaPow_add, omegaPow_neg]

/-! ### Eigenmodes -/

noncomputable def eigenmode (j : Fin 5) : VertexSpace :=
  fun x => omegaPow (j * x)

@[simp] theorem eigenmode_apply (j x : Fin 5) : eigenmode j x = omegaPow (j * x) := rfl

theorem eigenmode_zero : eigenmode 0 = constantVector 1 := by
  funext x; simp [eigenmode, constantVector, omegaPow]

theorem eigenmode_zero_apply (x : Fin 5) : eigenmode 0 x = 1 := by
  simp [eigenmode_zero, constantVector]

theorem d5Pull_r_eigenmode (j k : Fin 5) :
    d5Pull (r (k : ZMod 5)) (eigenmode j) = omegaPow (-(j * k)) • eigenmode j := by
  ext x
  simp only [d5Pull_r_apply, eigenmode_apply, Pi.smul_apply, smul_eq_mul]
  have hidx : j * (x - k) = -(j * k) + j * x := by
    rw [mul_sub, sub_eq_add_neg, add_comm]
  rw [hidx, omegaPow_add, mul_comm]

theorem d5Pull_r_one_eigenmode (j : Fin 5) :
    d5Pull (r (1 : ZMod 5)) (eigenmode j) = omegaPow (-j) • eigenmode j := by
  have h := d5Pull_r_eigenmode j (1 : Fin 5)
  rw [mul_one j] at h
  exact h

/-! ### Character sums -/

theorem sum_omegaPow_zero :
    ∑ x : Fin 5, omegaPow ((0 : Fin 5) * x) = (5 : ℂ) := by
  simp [omegaPow]

theorem sum_omegaPow_ne_zero {a : Fin 5} (ha : a ≠ 0) :
    ∑ x : Fin 5, omegaPow (a * x) = 0 := by
  have hcop : Nat.Coprime a.val 5 := by
    fin_cases a
    · exact absurd rfl ha
    · decide
    · decide
    · decide
    · decide
  have hprim : IsPrimitiveRoot (ω ^ a.val) 5 :=
    omega_isPrimitiveRoot.pow_of_coprime a.val hcop
  have hgeom : ∑ i ∈ Finset.range 5, (ω ^ a.val) ^ i = 0 :=
    IsPrimitiveRoot.geom_sum_eq_zero hprim (by decide)
  have hreindex :
      ∑ x : Fin 5, omegaPow (a * x) = ∑ i ∈ Finset.range 5, (ω ^ a.val) ^ i := by
    simp only [omegaPow]
    refine Finset.sum_bij (fun x _ => (x : ℕ))
      (fun x _ => Finset.mem_range.mpr x.isLt)
      (fun x y _ _ h => Fin.ext h)
      (fun i hi => ⟨⟨i, Finset.mem_range.mp hi⟩, Finset.mem_univ _, rfl⟩)
      (fun x _ => by
        have hmul : (a * x).val ≡ a.val * x.val [MOD 5] := by
          rw [Fin.val_mul]; exact Nat.mod_modEq _ 5
        exact (omega_pow_modEq hmul).trans (by rw [pow_mul]))
  rw [hreindex, hgeom]

theorem sum_omegaPow (a : Fin 5) :
    ∑ x : Fin 5, omegaPow (a * x) = if a = 0 then (5 : ℂ) else 0 := by
  split_ifs with ha
  · subst ha; exact sum_omegaPow_zero
  · exact sum_omegaPow_ne_zero ha

theorem character_orthogonality (j ℓ : Fin 5) :
    (5 : ℂ)⁻¹ * ∑ k : Fin 5, omegaPow ((j - ℓ) * k) =
      if j = ℓ then 1 else 0 := by
  rw [sum_omegaPow]
  by_cases hjl : j = ℓ
  · subst hjl
    -- (5)⁻¹ * (if 0=0 then 5 else 0) = 1
    simp only [sub_self, ite_true]
    exact inv_mul_cancel₀ (by norm_num : (5 : ℂ) ≠ 0)
  · have hsub : j - ℓ ≠ 0 := fun h => hjl (sub_eq_zero.mp h)
    simp only [hsub, hjl, ite_false, mul_zero]

theorem coordSum_eigenmode (j : Fin 5) :
    coordSum (eigenmode j) = if j = 0 then (5 : ℂ) else 0 := by
  -- `coordSum (eigenmode j) = ∑_x omegaPow (j * x)`
  change ∑ x : Fin 5, omegaPow (j * x) = if j = 0 then (5 : ℂ) else 0
  exact sum_omegaPow j

theorem eigenmode_mem_zeroSumSubmodule {j : Fin 5} (hj : j ≠ 0) :
    eigenmode j ∈ zeroSumSubmodule := by
  change coordSumLinear (eigenmode j) = 0
  rw [coordSumLinear_apply, coordSum_eigenmode, if_neg hj]

/-! ### Projector diagonalizes eigenmodes -/

noncomputable def isotypicProjector (j : Fin 5) (f : VertexSpace) : VertexSpace :=
  (5 : ℂ)⁻¹ • ∑ k : Fin 5, omegaPow (j * k) • d5Pull (r (k : ZMod 5)) f

theorem isotypicProjector_eigenmode (j ℓ : Fin 5) :
    isotypicProjector j (eigenmode ℓ) =
      (if j = ℓ then (1 : ℂ) else 0) • eigenmode ℓ := by
  have hterm (k : Fin 5) :
      omegaPow (j * k) • d5Pull (r (k : ZMod 5)) (eigenmode ℓ) =
        omegaPow ((j - ℓ) * k) • eigenmode ℓ := by
    rw [d5Pull_r_eigenmode, smul_smul]
    have : omegaPow (j * k) * omegaPow (-(ℓ * k)) = omegaPow ((j - ℓ) * k) := by
      rw [← omegaPow_add, ← sub_eq_add_neg, ← sub_mul]
    rw [this]
  simp only [isotypicProjector, hterm]
  rw [← Finset.sum_smul, smul_smul]
  exact congrArg (fun c : ℂ => c • eigenmode ℓ) (character_orthogonality j ℓ)

theorem isotypicProjector_eigenmode_self (j : Fin 5) :
    isotypicProjector j (eigenmode j) = eigenmode j := by
  rw [isotypicProjector_eigenmode, if_pos rfl, one_smul]

theorem isotypicProjector_eigenmode_of_ne {j ℓ : Fin 5} (h : j ≠ ℓ) :
    isotypicProjector j (eigenmode ℓ) = 0 := by
  rw [isotypicProjector_eigenmode, if_neg h, zero_smul]

end Brockian.D5Isotypic
