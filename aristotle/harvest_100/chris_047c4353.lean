/-
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Phys

open Complex

/-- The translation operator `(T_a φ)(x) = φ (x + a)`, as a `ℂ`-linear map on wavefunctions. -/
noncomputable def transl (a : ℝ) : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun φ := fun x => φ (x + a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma transl_apply (a : ℝ) (φ : ℝ → ℂ) (x : ℝ) : transl a φ x = φ (x + a) := rfl

/-- Iterating the translation eigenvalue relation `ψ (x + a) = c * ψ x`. -/
private lemma transl_iterate {a : ℝ} {ψ : ℝ → ℂ} {c : ℂ}
    (hstep : ∀ x, ψ (x + a) = c * ψ x) : ∀ (n : ℕ) (x : ℝ), ψ (x + n * a) = c ^ n * ψ x := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    have h : x + ((n + 1 : ℕ) : ℝ) * a = (x + n * a) + a := by push_cast; ring
    rw [h, hstep, ih]
    ring

/-- A bounded solution of `ψ (x + a) = c * ψ x` that does not vanish identically forces the
translation eigenvalue `c` to be a phase, `‖c‖ = 1`. -/
private lemma norm_eq_one_of_bounded {a : ℝ} {ψ : ℝ → ℂ} {c : ℂ} {C : ℝ} {x₀ : ℝ}
    (hstep : ∀ x, ψ (x + a) = c * ψ x) (hbdd : ∀ x, ‖ψ x‖ ≤ C) (hx₀ : ψ x₀ ≠ 0) (hc : c ≠ 0) :
    ‖c‖ = 1 := by
  have hA0 : 0 < ‖ψ x₀‖ := norm_pos_iff.mpr hx₀
  have hC0 : 0 < C := lt_of_lt_of_le hA0 (hbdd x₀)
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hle : ‖c‖ ≤ 1 := by
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / ‖ψ x₀‖) h
    have h1 : ‖ψ (x₀ + n * a)‖ = ‖c‖ ^ n * ‖ψ x₀‖ := by
      rw [transl_iterate hstep n x₀, norm_mul, norm_pow]
    have h2 := hbdd (x₀ + n * a)
    rw [h1] at h2
    have h3 : C / ‖ψ x₀‖ * ‖ψ x₀‖ < ‖c‖ ^ n * ‖ψ x₀‖ := mul_lt_mul_of_pos_right hn hA0
    rw [div_mul_cancel₀ _ (ne_of_gt hA0)] at h3
    linarith
  have hge : 1 ≤ ‖c‖ := by
    by_contra h
    push_neg at h
    have h1 : 1 < 1 / ‖c‖ := by rw [lt_div_iff₀ hcpos]; linarith
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / ‖ψ x₀‖) h1
    rw [one_div] at hn
    have hcn : (0:ℝ) < ‖c‖ ^ n := pow_pos hcpos n
    have key : ψ x₀ = c ^ n * ψ (x₀ - n * a) := by
      have h2 := transl_iterate hstep n (x₀ - n * a)
      simpa using h2
    have h2 : ‖ψ x₀‖ ≤ ‖c‖ ^ n * C := by
      rw [key, norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (hbdd _) (le_of_lt hcn)
    rw [inv_pow, ← one_div, div_lt_div_iff₀ hA0 hcn] at hn
    nlinarith
  linarith

/-- **Bloch's theorem.**  Let `H` be a linear Hamiltonian acting on wavefunctions `ℝ → ℂ` which
is periodic with period `a > 0`, i.e. it commutes with the translation operator `transl a`.
Let `ψ` be a nonzero bounded eigenstate of `H` with eigenvalue `E`, whose eigenspace is
nondegenerate (one-dimensional).  Then `ψ` is a Bloch wave: there exist a crystal momentum
`k : ℝ` and an `a`-periodic envelope `u` with `ψ x = e ^ (i * k * x) * u x` for all `x`. -/
theorem bloch_theorem (a : ℝ) (ha : 0 < a)
    (H : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ))
    (hperiodic : ∀ φ : ℝ → ℂ, H (transl a φ) = transl a (H φ))
    (ψ : ℝ → ℂ) (E : ℂ) (hψ : H ψ = E • ψ) (hne : ψ ≠ 0)
    (C : ℝ) (hbdd : ∀ x, ‖ψ x‖ ≤ C)
    (hnondeg : ∀ φ : ℝ → ℂ, H φ = E • φ → ∃ z : ℂ, φ = z • ψ) :
    ∃ (k : ℝ) (u : ℝ → ℂ), Function.Periodic u a ∧
      ∀ x, ψ x = Complex.exp (k * x * Complex.I) * u x := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  -- The translate of an eigenstate is again an eigenstate with the same eigenvalue.
  have hT : H (transl a ψ) = E • transl a ψ := by
    rw [hperiodic ψ, hψ]; ext x; simp
  obtain ⟨c, hc⟩ := hnondeg _ hT
  have hstep : ∀ x, ψ (x + a) = c * ψ x := by
    intro x; have h := congrFun hc x; simpa using h
  obtain ⟨x₀, hx₀⟩ : ∃ x, ψ x ≠ 0 := by
    by_contra h; push_neg at h; exact hne (funext fun x => h x)
  have hcne : c ≠ 0 := by
    intro h
    apply hx₀
    have h2 := hstep (x₀ - a)
    rw [h] at h2
    simpa using h2
  have hnorm : ‖c‖ = 1 := norm_eq_one_of_bounded hstep hbdd hx₀ hcne
  obtain ⟨θ, hcexp⟩ : ∃ t : ℝ, c = Complex.exp (t * Complex.I) :=
    ⟨Complex.arg c, by
      have h := Complex.norm_mul_exp_arg_mul_I c
      rw [hnorm] at h
      simpa using h.symm⟩
  refine ⟨θ / a, fun x => Complex.exp (-((θ / a : ℝ) * x) * Complex.I) * ψ x, ?_, ?_⟩
  · intro x
    have harg : -(((θ:ℂ)/a) * ((x:ℂ) + a)) * Complex.I + (θ:ℂ) * Complex.I
        = -(((θ:ℂ)/a) * (x:ℂ)) * Complex.I := by
      field_simp; ring
    push_cast
    rw [hstep x, hcexp, ← mul_assoc, ← Complex.exp_add, harg]
  · intro x
    push_cast
    rw [← mul_assoc, ← Complex.exp_add]
    ring_nf
    simp

end Phys

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

