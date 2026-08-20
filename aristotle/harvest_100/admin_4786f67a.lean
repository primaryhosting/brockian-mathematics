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

set_option autoImplicit false

namespace Phys

open Complex

/-- Translation of a wavefunction by `a`: `(translate a ψ) x = ψ (x + a)`. -/
def translate (a : ℝ) (ψ : ℝ → ℂ) : ℝ → ℂ := fun x => ψ (x + a)

/-- An operator `H` on wavefunctions is `a`-periodic when it commutes with translation
by the lattice constant `a`. -/
def PeriodicOperator (a : ℝ) (H : (ℝ → ℂ) → (ℝ → ℂ)) : Prop :=
  ∀ ψ : ℝ → ℂ, H (translate a ψ) = translate a (H ψ)

/-- If the Hamiltonian is periodic, translating an eigenstate produces an eigenstate with the
same energy.  (This is the reason one may diagonalize `H` and the translation operator
simultaneously, which is the hypothesis `hT` of `bloch_theorem` below.) -/
theorem translate_eigenstate_of_periodic {a : ℝ} {H : (ℝ → ℂ) → (ℝ → ℂ)}
    (hH : PeriodicOperator a H) {ψ : ℝ → ℂ} {E : ℂ} (hψ : H ψ = fun x => E * ψ x) :
    H (translate a ψ) = fun x => E * (translate a ψ) x := by
  rw [hH ψ, hψ]
  rfl

/-- Iterating the translation eigenvalue equation: `ψ (x + n a) = lam ^ n * ψ x`. -/
theorem translate_iterate {a : ℝ} {ψ : ℝ → ℂ} {lam : ℂ}
    (hT : ∀ x : ℝ, ψ (x + a) = lam * ψ x) (n : ℕ) (x : ℝ) :
    ψ (x + n * a) = lam ^ n * ψ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      have hx : x + ((n + 1 : ℕ) : ℝ) * a = (x + n * a) + a := by push_cast; ring
      rw [hx, hT, ih]
      ring

/-- The translation eigenvalue of a bounded, not identically vanishing eigenstate has modulus
one.  (Physically this is unitarity of the translation operator; here it is derived from
boundedness of `ψ`.) -/
theorem norm_translation_eigenvalue_eq_one {a : ℝ} {ψ : ℝ → ℂ} {lam : ℂ} {M : ℝ} {x₀ : ℝ}
    (hT : ∀ x : ℝ, ψ (x + a) = lam * ψ x) (hM : ∀ x : ℝ, ‖ψ x‖ ≤ M) (hx₀ : ψ x₀ ≠ 0) :
    ‖lam‖ = 1 := by
  have hpos : 0 < ‖ψ x₀‖ := norm_pos_iff.mpr hx₀
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM x₀)
  have hnorm : ∀ (n : ℕ) (x : ℝ), ‖ψ (x + n * a)‖ = ‖lam‖ ^ n * ‖ψ x‖ := by
    intro n x
    rw [translate_iterate hT n x, norm_mul, norm_pow]
  have hle : ‖lam‖ ≤ 1 := by
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / ‖ψ x₀‖) h
    rw [div_lt_iff₀ hpos] at hn
    have h2 := hM (x₀ + n * a)
    rw [hnorm n x₀] at h2
    linarith
  have hge : 1 ≤ ‖lam‖ := by
    by_contra h
    push_neg at h
    have hMpos : 0 < M + 1 := by linarith
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hpos hMpos) h
    have key : ‖ψ x₀‖ = ‖lam‖ ^ n * ‖ψ (x₀ - n * a)‖ := by
      have := hnorm n (x₀ - n * a)
      simpa using this
    have hb : ‖ψ (x₀ - n * a)‖ ≤ M := hM _
    have hpow : (0:ℝ) ≤ ‖lam‖ ^ n := pow_nonneg (norm_nonneg lam) n
    rw [lt_div_iff₀ hMpos] at hn
    nlinarith
  exact le_antisymm hle hge

/--
**Bloch's theorem.**  Let `a ≠ 0` be the lattice period and let `ψ` be a simultaneous
eigenstate of a periodic Hamiltonian and of the translation operator `T_a`, with eigenvalue
`lam` of unit modulus (as is forced by unitarity of `T_a`).  Then there is a crystal momentum
`k : ℝ` and an `a`-periodic function `u` such that

  `ψ x = e^{i k x} * u x`,   `u (x + a) = u x`,   `lam = e^{i k a}`,

i.e. `ψ` is a Bloch wave.

The key Mathlib ingredient is `Complex.norm_eq_one_iff`, which writes a unit-modulus
complex number as `exp (θ * I)`.
-/
theorem bloch_theorem (a : ℝ) (ha : a ≠ 0) (ψ : ℝ → ℂ) (lam : ℂ) (hlam : ‖lam‖ = 1)
    (hT : translate a ψ = fun x => lam * ψ x) :
    ∃ (k : ℝ) (u : ℝ → ℂ),
      (∀ x : ℝ, u (x + a) = u x) ∧
      (∀ x : ℝ, ψ x = Complex.exp (k * x * I) * u x) ∧
      lam = Complex.exp (k * a * I) := by
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff lam).mp hlam
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hka : (((θ / a : ℝ) : ℂ)) * (a : ℂ) = (θ : ℂ) := by
    push_cast
    field_simp
  have hinv : Complex.exp (-((θ : ℂ) * I)) * Complex.exp ((θ : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]
    simp
  refine ⟨θ / a, fun x => Complex.exp (-((θ / a : ℝ) * x * I)) * ψ x, ?_, ?_, ?_⟩
  · intro x
    have hψ : ψ (x + a) = lam * ψ x := congrFun hT x
    show Complex.exp (-(((θ / a : ℝ) : ℂ) * ((x + a : ℝ) : ℂ) * I)) * ψ (x + a)
        = Complex.exp (-(((θ / a : ℝ) : ℂ) * (x : ℂ) * I)) * ψ x
    rw [hψ, ← hθ, Complex.ofReal_add,
      show -(((θ / a : ℝ) : ℂ) * ((x : ℂ) + (a : ℂ)) * I)
          = -(((θ / a : ℝ) : ℂ) * (x : ℂ) * I) + -(((θ / a : ℝ) : ℂ) * (a : ℂ) * I) by ring,
      hka, Complex.exp_add, mul_assoc, ← mul_assoc (Complex.exp (-((θ : ℂ) * I))), hinv,
      one_mul]
  · intro x
    rw [← mul_assoc, ← Complex.exp_add]
    simp
  · rw [← hθ, hka]

/--
**Bloch's theorem, with unit modulus derived.**  If `ψ` is a bounded, not identically zero
eigenstate of the translation operator `T_a` with `a ≠ 0` (the situation for an eigenstate of
a Hamiltonian commuting with `T_a`, cf. `Phys.translate_eigenstate_of_periodic`), then `ψ` is
a Bloch wave `e^{i k x} u (x)` with `u` `a`-periodic.  Here the unit modulus of the
translation eigenvalue is *derived* from boundedness of `ψ` rather than assumed.
-/
theorem bloch_theorem_of_bounded {a : ℝ} (ha : a ≠ 0) {ψ : ℝ → ℂ} {lam : ℂ} {M x₀ : ℝ}
    (hT : translate a ψ = fun x => lam * ψ x)
    (hM : ∀ x : ℝ, ‖ψ x‖ ≤ M) (hx₀ : ψ x₀ ≠ 0) :
    ∃ (k : ℝ) (u : ℝ → ℂ),
      (∀ x : ℝ, u (x + a) = u x) ∧
      (∀ x : ℝ, ψ x = Complex.exp (k * x * I) * u x) ∧
      lam = Complex.exp (k * a * I) := by
  have hlam : ‖lam‖ = 1 :=
    norm_translation_eigenvalue_eq_one (fun x => congrFun hT x) hM hx₀
  exact bloch_theorem a ha ψ lam hlam hT

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

