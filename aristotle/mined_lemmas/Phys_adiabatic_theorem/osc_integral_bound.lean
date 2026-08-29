import Mathlib

/-!
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

open Complex MeasureTheory intervalIntegral
open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Phases -/

/-- The unimodular phase `u ↦ exp (i r u)`. -/

theorem osc_integral_bound [CompleteSpace E] (f Df : ℝ → E)
    (hf : ∀ u, HasDerivAt f (Df u) u) (hDf : Continuous Df) (ω A B : ℝ) (hω : ω ≠ 0)
    (hA : ∀ u ∈ Set.Icc (0:ℝ) 1, ‖f u‖ ≤ A)
    (hB : ∀ u ∈ Set.Icc (0:ℝ) 1, ‖Df u‖ ≤ B) (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    ‖∫ u in (0:ℝ)..s, cphase ω u • f u‖ ≤ (2 * A + B) / |ω| := by
  obtain ⟨hs0, hs1⟩ := hs
  have hf_cont : Continuous f := continuous_iff_continuousAt.mpr fun u => (hf u).continuousAt
  set k : ℂ := (ω : ℂ) * Complex.I with hk
  have hkne : k ≠ 0 := by
    simp only [hk, ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
    exact hω
  have hknorm : ‖k‖ = |ω| := by simp [hk]
  set F : ℝ → E := fun u => (cphase ω u / k) • f u with hF
  have hFd : ∀ u, HasDerivAt F (cphase ω u • f u + (cphase ω u / k) • Df u) u := by
    intro u
    have h1 : HasDerivAt (fun t => cphase ω t / k) (cphase ω u * k / k) u :=
      (cphase_hasDerivAt ω u).div_const k
    refine (h1.smul (hf u)).congr_deriv ?_
    rw [mul_div_assoc, div_self hkne, mul_one]
    abel
  have hg1 : Continuous (fun u => cphase ω u • f u) := (cphase_continuous ω).smul hf_cont
  have hg2 : Continuous (fun u => (cphase ω u / k) • Df u) :=
    ((cphase_continuous ω).div_const k).smul hDf
  have hint : ∫ u in (0:ℝ)..s, (cphase ω u • f u + (cphase ω u / k) • Df u) = F s - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hFd x)
      ((hg1.add hg2).intervalIntegrable _ _)
  rw [intervalIntegral.integral_add (hg1.intervalIntegrable _ _)
    (hg2.intervalIntegrable _ _)] at hint
  have hsplit : ∫ u in (0:ℝ)..s, cphase ω u • f u
      = (F s - F 0) - ∫ u in (0:ℝ)..s, (cphase ω u / k) • Df u := by
    rw [← hint]; abel
  have hsub : Set.uIoc (0:ℝ) s ⊆ Set.Icc (0:ℝ) 1 := by
    intro x hx
    rw [Set.uIoc_of_le hs0] at hx
    exact ⟨le_of_lt hx.1, hx.2.trans hs1⟩
  have hωpos : (0:ℝ) < |ω| := abs_pos.mpr hω
  have hFbound : ∀ u ∈ Set.Icc (0:ℝ) 1, ‖F u‖ ≤ A / |ω| := by
    intro u hu
    rw [hF]
    simp only [norm_smul, norm_div, norm_cphase, hknorm]
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff_of_pos_right hωpos]
    exact hA u hu
  have hDbound : ‖∫ u in (0:ℝ)..s, (cphase ω u / k) • Df u‖ ≤ (B / |ω|) * |s - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro x hx
    have hx' := hB x (hsub hx)
    simp only [norm_smul, norm_div, norm_cphase, hknorm]
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff_of_pos_right hωpos]
    exact hx'
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 ⟨le_refl 0, zero_le_one⟩)
  have hs' : |s - 0| ≤ 1 := by rw [sub_zero, abs_of_nonneg hs0]; exact hs1
  have h1 := hFbound s ⟨hs0, hs1⟩
  have h2 := hFbound 0 ⟨le_refl 0, zero_le_one⟩
  have h3 : (B / |ω|) * |s - 0| ≤ B / |ω| := by
    nlinarith [div_nonneg hB0 (le_of_lt hωpos), abs_nonneg (s - 0)]
  calc ‖∫ u in (0:ℝ)..s, cphase ω u • f u‖
      ≤ ‖F s - F 0‖ + ‖∫ u in (0:ℝ)..s, (cphase ω u / k) • Df u‖ := by
        rw [hsplit]; exact norm_sub_le _ _
    _ ≤ (‖F s‖ + ‖F 0‖) + (B / |ω|) * |s - 0| := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ (A / |ω| + A / |ω|) + B / |ω| := by gcongr
    _ = (2 * A + B) / |ω| := by ring

/-! ## The adiabatic theorem -/

/-- **Adiabatic theorem.**

Let `P s` be a smoothly varying orthogonal projection (`P s` idempotent and self-adjoint) onto a
nondegenerate instantaneous eigenspace, and let
`ham P e₁ e₂ s = e₁ • P s + e₂ • (1 - P s)` be the corresponding instantaneous Hamiltonian, whose
eigenvalue `e₁` on `range (P s)` is separated by the spectral gap `e₂ - e₁ ≠ 0` from the rest of
the spectrum.

If `ψ` solves the Schrödinger equation `ε • ψ' = -i • ham ψ` -- i.e. the Hamiltonian is traversed
over a physical time `1/ε`, so that it varies ever more slowly as `ε → 0` -- and if the initial
state lies in the initial eigenspace (`P 0 (ψ 0) = ψ 0`), then, throughout the whole evolution, the
state stays in the instantaneous eigenspace `range (P s)` up to an error `O(ε)`: the transverse
component `ψ s - P s (ψ s)` is bounded by `C * ε * ‖ψ 0‖` with a constant `C` depending only on
the Hamiltonian, not on `ε` or on the solution. -/
