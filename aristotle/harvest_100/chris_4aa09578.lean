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

Eigenstates of a periodic Hamiltonian are Bloch waves `e^{ikx} u_k(x)`.

The development is organised as follows.

* `Phys.schrodinger` : the one-dimensional Schrödinger operator `ψ ↦ -ψ'' + V ψ`.
* `Phys.IsEigenstate` : `ψ` solves `-ψ'' + V ψ = E ψ`.
* `Phys.isEigenstate_translate` : the Hamiltonian commutes with translation by a period of `V`.
* `Phys.norm_eq_one_of_bounded` : a bounded nonzero `ψ` with `ψ (x + a) = c ψ (x)` has `‖c‖ = 1`.
* `Phys.bloch_theorem` : the main result.
* `Phys.bloch_theorem_of_translation_eigenvalue` : the same conclusion starting directly from
  the translation-eigenvalue property.
* `Phys.bloch_hypotheses_satisfiable` : the hypotheses of `bloch_theorem` are consistent
  (they are met by the constant potential with the constant eigenstate).
-/

namespace Phys

open Complex

/-- The one-dimensional Schrödinger operator with potential `V` (units `ℏ²/2m = 1`),
acting on functions `ψ : ℝ → ℂ`. -/
noncomputable def schrodinger (V : ℝ → ℂ) (psi : ℝ → ℂ) : ℝ → ℂ :=
  fun x => -deriv (deriv psi) x + V x * psi x

/-- `psi` is an eigenstate of the Schrödinger operator with potential `V` and energy `E`. -/
def IsEigenstate (V : ℝ → ℂ) (E : ℂ) (psi : ℝ → ℂ) : Prop :=
  ∀ x, schrodinger V psi x = E * psi x

/-- Translating a solution of the Schrödinger equation by a period of the potential
again gives a solution: the Hamiltonian commutes with the lattice translation. -/
theorem isEigenstate_translate {a : ℝ} {V : ℝ → ℂ} (hV : ∀ x, V (x + a) = V x)
    {E : ℂ} {psi : ℝ → ℂ} (h : IsEigenstate V E psi) :
    IsEigenstate V E (fun y => psi (y + a)) := by
  have h1 : deriv (fun y => psi (y + a)) = fun y => deriv psi (y + a) := by
    funext y
    exact deriv_comp_add_const psi a y
  have h2 : deriv (deriv (fun y => psi (y + a))) = fun y => deriv (deriv psi) (y + a) := by
    rw [h1]
    funext y
    exact deriv_comp_add_const (deriv psi) a y
  intro x
  have hx := h (x + a)
  simp only [schrodinger, h2, hV x] at *
  linear_combination hx

/-- If `ψ (x + a) = c * ψ x` for all `x`, then `ψ (x + n * a) = c ^ n * ψ x`. -/
theorem iterate_translate {a : ℝ} {c : ℂ} {psi : ℝ → ℂ}
    (hc : ∀ x, psi (x + a) = c * psi x) (n : ℕ) (x : ℝ) :
    psi (x + n * a) = c ^ n * psi x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : (x + (n : ℝ) * a) + a = x + ((n : ℕ) + 1 : ℕ) * a := by push_cast; ring
      calc psi (x + ((n : ℕ) + 1 : ℕ) * a) = psi ((x + (n : ℝ) * a) + a) := by rw [hstep]
        _ = c * psi (x + (n : ℝ) * a) := hc _
        _ = c * (c ^ n * psi x) := by rw [ih]
        _ = c ^ (n + 1) * psi x := by ring

/-- A bounded, nonzero function satisfying `ψ (x + a) = c * ψ x` forces `‖c‖ = 1`:
the translation eigenvalue is a pure phase. -/
theorem norm_eq_one_of_bounded {a : ℝ} {c : ℂ} {psi : ℝ → ℂ}
    (hc : ∀ x, psi (x + a) = c * psi x)
    (hne : ∃ x₀, psi x₀ ≠ 0) (hbdd : ∃ C, ∀ x, ‖psi x‖ ≤ C) :
    ‖c‖ = 1 := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨C, hC⟩ := hbdd
  set M := ‖psi x₀‖ with hM
  have hM0 : 0 < M := norm_pos_iff.mpr hx₀
  have hMC : M ≤ C := hC x₀
  have hC0 : 0 < C := lt_of_lt_of_le hM0 hMC
  have key : ∀ n : ℕ, ‖c‖ ^ n * M ≤ C := by
    intro n
    have h := iterate_translate hc n x₀
    have hnorm : ‖c‖ ^ n * M = ‖psi (x₀ + n * a)‖ := by
      rw [h, norm_mul, norm_pow]
    rw [hnorm]
    exact hC _
  have key2 : ∀ n : ℕ, M ≤ ‖c‖ ^ n * C := by
    intro n
    have h := iterate_translate hc n (x₀ - n * a)
    have hx : x₀ - (n : ℝ) * a + n * a = x₀ := by ring
    rw [hx] at h
    have hnorm : M = ‖c‖ ^ n * ‖psi (x₀ - n * a)‖ := by
      rw [hM, h, norm_mul, norm_pow]
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left (hC _) (by positivity)
  have hle : ‖c‖ ≤ 1 := by
    by_contra hgt
    push_neg at hgt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / M) hgt
    have h2 : C < ‖c‖ ^ n * M := by
      rw [div_lt_iff₀ hM0] at hn
      linarith
    linarith [key n]
  have hge : 1 ≤ ‖c‖ := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < M / C by positivity) hlt
    have h2 : ‖c‖ ^ n * C < M := by
      rw [lt_div_iff₀ hC0] at hn
      linarith
    linarith [key2 n]
  linarith

/-- **Bloch's theorem, translation-eigenvalue form.**  A bounded nonzero function which is an
eigenvector of the translation by `a > 0` is a Bloch wave: `ψ x = e^{i k x} u x` with `u`
`a`-periodic. -/
theorem bloch_theorem_of_translation_eigenvalue {a : ℝ} (ha : 0 < a) {c : ℂ} {psi : ℝ → ℂ}
    (hc : ∀ x, psi (x + a) = c * psi x)
    (hne : ∃ x₀, psi x₀ ≠ 0) (hbdd : ∃ C, ∀ x, ‖psi x‖ ≤ C) :
    ∃ (k : ℝ) (u : ℝ → ℂ), (∀ x, u (x + a) = u x) ∧
      ∀ x, psi x = Complex.exp (Complex.I * k * x) * u x := by
  have hcnorm : ‖c‖ = 1 := norm_eq_one_of_bounded hc hne hbdd
  refine ⟨Complex.arg c / a, fun x => Complex.exp (-(Complex.I * (Complex.arg c / a) * x)) * psi x,
    ?_, ?_⟩
  · intro x
    have ha0 : (a : ℂ) ≠ 0 := by
      simpa using ne_of_gt ha
    have hc0 : c ≠ 0 := by
      intro h
      rw [h] at hcnorm
      simp at hcnorm
    have hexp : Complex.exp (Complex.I * ((Complex.arg c : ℂ) / a) * a) = c := by
      have h1 : Complex.I * ((Complex.arg c : ℂ) / a) * a = (Complex.arg c : ℂ) * Complex.I := by
        field_simp
      rw [h1]
      have h2 := Complex.norm_mul_exp_arg_mul_I c
      rw [hcnorm] at h2
      simpa using h2
    have hx : (-(Complex.I * ((Complex.arg c : ℂ) / a) * ((x : ℂ) + a)))
        = (-(Complex.I * ((Complex.arg c : ℂ) / a) * x))
          + (-(Complex.I * ((Complex.arg c : ℂ) / a) * a)) := by
      ring
    have hshift : Complex.exp (-(Complex.I * ((Complex.arg c : ℂ) / a) * ((x : ℂ) + a)))
        = Complex.exp (-(Complex.I * ((Complex.arg c : ℂ) / a) * x)) * c⁻¹ := by
      rw [hx, Complex.exp_add]
      congr 1
      rw [Complex.exp_neg, hexp]
    simp only [hc x, Complex.ofReal_add, hshift]
    field_simp
  · intro x
    rw [← mul_assoc, ← Complex.exp_add]
    simp

/-- **Bloch's theorem.**  Let `V` be a potential periodic with period `a > 0`, and let `ψ`
be a `C²`, bounded, nonzero eigenstate of the corresponding Schrödinger operator
`-ψ'' + V ψ = E ψ`, whose space of bounded `C²` eigenstates at energy `E` is one-dimensional
(spanned by `ψ`).  Then `ψ` is a Bloch wave: there are a crystal momentum `k : ℝ` and an
`a`-periodic function `u` with `ψ x = e^{i k x} * u x`. -/
theorem bloch_theorem {a : ℝ} (ha : 0 < a) {V : ℝ → ℂ} (hV : ∀ x, V (x + a) = V x)
    {E : ℂ} {psi : ℝ → ℂ} (hsmooth : ContDiff ℝ 2 psi) (hpsi : IsEigenstate V E psi)
    (hne : ∃ x₀, psi x₀ ≠ 0) (hbdd : ∃ C, ∀ x, ‖psi x‖ ≤ C)
    (hnondeg : ∀ φ : ℝ → ℂ, ContDiff ℝ 2 φ → IsEigenstate V E φ →
      (∃ C, ∀ x, ‖φ x‖ ≤ C) → ∃ c : ℂ, ∀ x, φ x = c * psi x) :
    ∃ (k : ℝ) (u : ℝ → ℂ), (∀ x, u (x + a) = u x) ∧
      ∀ x, psi x = Complex.exp (Complex.I * k * x) * u x := by
  have hsmooth' : ContDiff ℝ 2 (fun y => psi (y + a)) :=
    hsmooth.comp (contDiff_id.add contDiff_const)
  have hbdd' : ∃ C, ∀ x, ‖psi (x + a)‖ ≤ C := by
    obtain ⟨C, hC⟩ := hbdd
    exact ⟨C, fun x => hC _⟩
  obtain ⟨c, hc⟩ := hnondeg _ hsmooth' (isEigenstate_translate hV hpsi) hbdd'
  exact bloch_theorem_of_translation_eigenvalue ha hc hne hbdd

/-- The hypotheses of `Phys.bloch_theorem` are consistent: they are satisfied by the vanishing
potential with energy `0` and the constant eigenstate `ψ ≡ 1`, for which the space of bounded
`C²` solutions of `-φ'' = 0` is indeed one-dimensional. -/
theorem bloch_hypotheses_satisfiable :
    ∃ (a : ℝ) (V : ℝ → ℂ) (E : ℂ) (psi : ℝ → ℂ),
      0 < a ∧ (∀ x, V (x + a) = V x) ∧ ContDiff ℝ 2 psi ∧ IsEigenstate V E psi ∧
      (∃ x₀, psi x₀ ≠ 0) ∧ (∃ C, ∀ x, ‖psi x‖ ≤ C) ∧
      (∀ φ : ℝ → ℂ, ContDiff ℝ 2 φ → IsEigenstate V E φ →
        (∃ C, ∀ x, ‖φ x‖ ≤ C) → ∃ c : ℂ, ∀ x, φ x = c * psi x) := by
  refine ⟨1, fun _ => 0, 0, fun _ => 1, one_pos, fun _ => rfl, contDiff_const, ?_,
    ⟨0, one_ne_zero⟩, ⟨1, fun _ => by simp⟩, ?_⟩
  · intro x
    simp [schrodinger]
  · rintro φ hφ hE ⟨C, hC⟩
    -- `φ'' = 0` pointwise
    have hzero : ∀ x, deriv (deriv φ) x = 0 := by
      intro x
      have := hE x
      simp only [schrodinger, zero_mul] at this
      simpa using this
    have hdiff1 : Differentiable ℝ φ := hφ.differentiable (by norm_num)
    have hdiff2 : Differentiable ℝ (deriv φ) := hφ.differentiable_deriv_two
    -- hence `φ'` is a constant `b`
    set b : ℂ := deriv φ 0 with hb
    have hconst : ∀ x, deriv φ x = b := fun x => is_const_of_deriv_eq_zero hdiff2 hzero x 0
    -- hence `φ x = φ 0 + b * x`
    have hlin : ∀ x : ℝ, φ x = φ 0 + b * x := by
      have hg : Differentiable ℝ (fun x : ℝ => φ x - b * (x : ℂ)) := by
        refine hdiff1.sub ?_
        intro x
        exact ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul b).differentiableAt
      have hgz : ∀ x : ℝ, deriv (fun x : ℝ => φ x - b * (x : ℂ)) x = 0 := by
        intro x
        have h1 : HasDerivAt (fun t : ℝ => b * (t : ℂ)) b x := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul b
        have h2 : HasDerivAt φ b x := by
          have := (hdiff1 x).hasDerivAt
          rwa [hconst x] at this
        simpa using (h2.sub h1).deriv
      intro x
      have := is_const_of_deriv_eq_zero hg hgz x 0
      simp only [Complex.ofReal_zero, mul_zero, sub_zero] at this
      linear_combination this
    -- boundedness forces `b = 0`
    have hb0 : b = 0 := by
      by_contra hbne
      have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hbne
      obtain ⟨n, hn⟩ := exists_nat_gt ((C + ‖φ 0‖) / ‖b‖)
      have hnb : C + ‖φ 0‖ < ‖b‖ * n := by
        rw [div_lt_iff₀ hbpos] at hn
        linarith
      have hle := hC (n : ℝ)
      rw [hlin (n : ℝ)] at hle
      have h1 : ‖b * ((n : ℝ) : ℂ)‖ - ‖φ 0‖ ≤ ‖φ 0 + b * ((n : ℝ) : ℂ)‖ := by
        have := norm_sub_norm_le (b * ((n : ℝ) : ℂ)) (-(φ 0))
        simpa [sub_neg_eq_add, add_comm] using this
      have h2 : ‖b * ((n : ℝ) : ℂ)‖ = ‖b‖ * n := by
        simp
      rw [h2] at h1
      linarith
    refine ⟨φ 0, fun x => ?_⟩
    rw [hlin x, hb0]
    ring

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

