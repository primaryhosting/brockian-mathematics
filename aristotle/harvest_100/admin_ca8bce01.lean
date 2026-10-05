/-
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

open Complex

/-- `f` has period `a`. -/
def IsPeriodic (a : ℝ) (f : ℝ → ℂ) : Prop := ∀ x, f (x + a) = f x

/-- `ψ` is an eigenstate of the one-dimensional Hamiltonian `H = -d²/dx² + V`
with energy `E`, i.e. `-ψ'' + V ψ = E ψ`, written as `ψ'' = (V - E) ψ`. -/
def SchrodingerEigenstate (V : ℝ → ℂ) (E : ℂ) (ψ : ℝ → ℂ) : Prop :=
  ∀ x, deriv (deriv ψ) x = (V x - E) * ψ x

/-- `ψ` is a Bloch wave for the lattice spacing `a`: `ψ x = e^{i k x} u x` with `u`
`a`-periodic. -/
def IsBlochWave (a : ℝ) (ψ : ℝ → ℂ) : Prop :=
  ∃ k : ℝ, ∃ u : ℝ → ℂ, IsPeriodic a u ∧ ∀ x, ψ x = Complex.exp (k * x * Complex.I) * u x

/-- Translating an eigenstate by a lattice vector gives another eigenstate,
because the potential is periodic. -/
theorem schrodingerEigenstate_shift {a : ℝ} {V : ℝ → ℂ} {E : ℂ} {ψ : ℝ → ℂ}
    (hV : IsPeriodic a V) (hψ : SchrodingerEigenstate V E ψ) :
    SchrodingerEigenstate V E (fun x => ψ (x + a)) := by
  intro x
  have h1 : deriv (fun y => ψ (y + a)) = fun y => deriv ψ (y + a) := by
    funext y
    exact deriv_comp_add_const ψ a y
  rw [h1]
  have h2 : deriv (fun y => deriv ψ (y + a)) x = deriv (deriv ψ) (x + a) :=
    deriv_comp_add_const (deriv ψ) a x
  rw [h2, hψ (x + a), hV x]

/-- Iterating the translation relation `ψ (x + a) = lam * ψ x`. -/
theorem translate_pow {a : ℝ} {ψ : ℝ → ℂ} {lam : ℂ}
    (h : ∀ x, ψ (x + a) = lam * ψ x) (n : ℕ) (x : ℝ) :
    ψ (x + n * a) = lam ^ n * ψ x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have : (x : ℝ) + (n + 1 : ℕ) * a = (x + n * a) + a := by push_cast; ring
      rw [this, h (x + n * a), ih]
      ring

/-- Backward iteration of the translation relation. -/
theorem translate_pow_neg {a : ℝ} {ψ : ℝ → ℂ} {lam : ℂ}
    (h : ∀ x, ψ (x + a) = lam * ψ x) (n : ℕ) (x : ℝ) :
    ψ x = lam ^ n * ψ (x - n * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hx : (x : ℝ) - (n : ℕ) * a = (x - (n + 1 : ℕ) * a) + a := by push_cast; ring
      rw [ih, hx, h]
      ring

/-- A bounded nonzero solution of the translation eigenvalue equation forces the
eigenvalue to be a unit modulus complex number. -/
theorem norm_translation_eigenvalue_eq_one {a : ℝ} {ψ : ℝ → ℂ} {lam : ℂ} {C : ℝ}
    (h : ∀ x, ψ (x + a) = lam * ψ x) (hbdd : ∀ x, ‖ψ x‖ ≤ C)
    {x₀ : ℝ} (hx₀ : ψ x₀ ≠ 0) : ‖lam‖ = 1 := by
  have hpos : 0 < ‖ψ x₀‖ := norm_pos_iff.mpr hx₀
  have hle : ‖lam‖ ≤ 1 := by
    by_contra hgt
    push_neg at hgt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / ‖ψ x₀‖) hgt
    have hkey : ‖lam‖ ^ n * ‖ψ x₀‖ ≤ C := by
      have := hbdd (x₀ + n * a)
      rwa [translate_pow h n x₀, norm_mul, norm_pow] at this
    have : C / ‖ψ x₀‖ < ‖lam‖ ^ n := hn
    rw [div_lt_iff₀ hpos] at this
    linarith [hkey, this]
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hbdd x₀)
  have hge : 1 ≤ ‖lam‖ := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := ‖ψ x₀‖ / (C + 1)) (y := ‖lam‖)
      (div_pos hpos (by linarith)) hlt
    have hkey : ‖ψ x₀‖ ≤ ‖lam‖ ^ n * C := by
      have h1 := translate_pow_neg h n x₀
      have h2 : ‖ψ x₀‖ = ‖lam‖ ^ n * ‖ψ (x₀ - n * a)‖ := by
        rw [h1, norm_mul, norm_pow]
      rw [h2]
      have := hbdd (x₀ - n * a)
      nlinarith [pow_nonneg (norm_nonneg lam) n, norm_nonneg (ψ (x₀ - (n:ℝ) * a))]
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < C + 1)] at hn
    nlinarith [pow_nonneg (norm_nonneg lam) n]
  linarith

/-- **Bloch's theorem.**  Let `V` be a potential periodic with period `a ≠ 0` and let `ψ`
be a bounded, nonzero eigenstate of the Hamiltonian `H = -d²/dx² + V` with energy `E`
whose eigenspace is nondegenerate (any eigenstate with the same energy is a multiple of
`ψ`).  Then `ψ` is a Bloch wave: `ψ x = e^{i k x} u x` with `u` periodic of period `a`. -/
theorem bloch_theorem {a : ℝ} (ha : a ≠ 0) {V ψ : ℝ → ℂ} {E : ℂ} {C : ℝ}
    (hV : IsPeriodic a V) (hψ : SchrodingerEigenstate V E ψ)
    (hne : ∃ x, ψ x ≠ 0) (hbdd : ∀ x, ‖ψ x‖ ≤ C)
    (hnondeg : ∀ φ : ℝ → ℂ, SchrodingerEigenstate V E φ → ∃ c : ℂ, ∀ x, φ x = c * ψ x) :
    IsBlochWave a ψ := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨lam, hlam⟩ := hnondeg _ (schrodingerEigenstate_shift hV hψ)
  have hnorm : ‖lam‖ = 1 := norm_translation_eigenvalue_eq_one hlam hbdd hx₀
  set θ : ℝ := Complex.arg lam with hθ
  have hca : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hexp : Complex.exp (θ * Complex.I) = lam := by
    have := Complex.norm_mul_exp_arg_mul_I lam
    rw [hnorm] at this
    simpa using this
  refine ⟨θ / a, fun x => Complex.exp (-(θ / a) * x * Complex.I) * ψ x, ?_, ?_⟩
  · intro x
    have h1 : ψ (x + a) = lam * ψ x := hlam x
    have h2 : -((θ : ℂ) / (a : ℂ)) * ((x + a : ℝ) : ℂ) * Complex.I
        = -((θ : ℂ) / (a : ℂ)) * (x : ℂ) * Complex.I + -((θ : ℂ) * Complex.I) := by
      push_cast
      field_simp
      ring
    have hinv : Complex.exp (-((θ : ℂ) * Complex.I)) * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]
      simp
    simp only [h1, h2, Complex.exp_add, ← hexp]
    linear_combination (Complex.exp (-((θ : ℂ) / (a : ℂ)) * (x : ℂ) * Complex.I) * ψ x) * hinv
  · intro x
    have h3 : ((θ / a : ℝ) : ℂ) * (x : ℂ) * Complex.I
        + -((θ : ℂ) / (a : ℂ)) * (x : ℂ) * Complex.I = 0 := by
      push_cast
      ring
    simp only [← mul_assoc, ← Complex.exp_add, h3, Complex.exp_zero, one_mul]

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

