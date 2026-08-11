/-
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Statement: Eigenstates of a periodic Hamiltonian are Bloch waves e^{ikx}u_k(x).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Statement: Eigenstates of a periodic Hamiltonian are Bloch waves e^{ikx}u_k(x).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-- The translation operator by a lattice period `a`, acting on wave functions
`ψ : ℝ → ℂ` by `(T_a ψ)(x) = ψ (x + a)`. -/
def translate (a : ℝ) (ψ : ℝ → ℂ) : ℝ → ℂ := fun x => ψ (x + a)

/-- A Hamiltonian `H` is *lattice periodic* with period `a` when it commutes with the
translation operator `translate a`. -/
def CommutesWithTranslation (a : ℝ) (H : (ℝ → ℂ) → (ℝ → ℂ)) : Prop :=
  ∀ ψ : ℝ → ℂ, H (translate a ψ) = translate a (H ψ)

/-- A Hamiltonian of the form `H = T + V` (a translation-invariant kinetic term `T`
plus multiplication by a potential `V` with period `a`) commutes with translation by `a`.
This justifies the hypothesis `CommutesWithTranslation` in Bloch's theorem. -/
theorem commutesWithTranslation_kinetic_add_periodic_potential
    {a : ℝ} (T : (ℝ → ℂ) → (ℝ → ℂ)) (V : ℝ → ℂ)
    (hT : CommutesWithTranslation a T) (hV : ∀ x, V (x + a) = V x) :
    CommutesWithTranslation a (fun ψ => fun x => T ψ x + V x * ψ x) := by
  intro ψ
  funext x
  have hTψ : T (translate a ψ) x = T ψ (x + a) := by
    rw [hT ψ]; rfl
  simp only [translate, hTψ, hV x]

/-- **Simultaneous diagonalization step.** If the Hamiltonian `H` commutes with translation
by `a` and `ψ` spans a (simple) eigenspace of `H` for the eigenvalue `E`, then `ψ` is also an
eigenfunction of the translation operator: `ψ (x + a) = c * ψ x` for some constant `c`. -/
theorem translation_eigenvalue_of_simple_eigenstate
    {a : ℝ} {H : (ℝ → ℂ) → (ℝ → ℂ)} {E : ℂ} {ψ : ℝ → ℂ}
    (hH : CommutesWithTranslation a H)
    (hEig : H ψ = fun x => E * ψ x)
    (hsimple : ∀ φ : ℝ → ℂ, (H φ = fun x => E * φ x) → ∃ c : ℂ, ∀ x, φ x = c * ψ x) :
    ∃ c : ℂ, ∀ x, ψ (x + a) = c * ψ x := by
  have hφ : H (translate a ψ) = fun x => E * translate a ψ x := by
    rw [hH ψ, hEig]
    rfl
  obtain ⟨c, hc⟩ := hsimple _ hφ
  exact ⟨c, hc⟩

/-- A complex number of modulus one is `exp (I * k * a)` for a real `k` (given `a ≠ 0`). -/
theorem exists_real_wavenumber {c : ℂ} (hc : ‖c‖ = 1) {a : ℝ} (ha : a ≠ 0) :
    ∃ k : ℝ, c = Complex.exp (Complex.I * k * a) := by
  refine ⟨Complex.arg c / a, ?_⟩
  have h := Complex.norm_mul_exp_arg_mul_I c
  rw [hc] at h
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hka : ((Complex.arg c / a : ℝ) : ℂ) * a = (Complex.arg c : ℂ) := by
    push_cast
    exact div_mul_cancel₀ _ ha'
  rw [mul_assoc, hka]
  conv_lhs => rw [← h]
  rw [mul_comm Complex.I]
  simp

/-- **Floquet/Bloch factorization.** A wave function satisfying the translation eigenvalue
relation `ψ (x + a) = e^{i k a} ψ (x)` is a Bloch wave: `ψ (x) = e^{i k x} u (x)` with `u`
periodic of period `a`. -/
theorem bloch_factorization {a k : ℝ} {ψ : ℝ → ℂ}
    (hψ : ∀ x, ψ (x + a) = Complex.exp (Complex.I * k * a) * ψ x) :
    ∃ u : ℝ → ℂ, (∀ x, u (x + a) = u x) ∧ ∀ x, ψ x = Complex.exp (Complex.I * k * x) * u x := by
  refine ⟨fun x => Complex.exp (-(Complex.I * k * x)) * ψ x, fun x => ?_, fun x => ?_⟩
  · dsimp only
    rw [hψ x, ← mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  · dsimp only
    rw [← mul_assoc, ← Complex.exp_add]
    simp

/-- **Bloch's theorem.**

Let `H` be a Hamiltonian on wave functions `ψ : ℝ → ℂ` which commutes with translation by the
lattice period `a ≠ 0` (for instance a kinetic term plus a periodic potential, see
`Phys.commutesWithTranslation_kinetic_add_periodic_potential`).  Let `ψ` be an eigenstate of `H`
with eigenvalue `E`, spanning its eigenspace, whose probability density `‖ψ‖²` is unchanged by
the lattice translation.

Then `ψ` is a *Bloch wave*: there is a real wavenumber `k` (the crystal momentum) and a
lattice-periodic function `u` such that

  `ψ (x) = e^{i k x} · u (x)`,  `u (x + a) = u (x)`,

and moreover `ψ` satisfies the Bloch boundary condition `ψ (x + a) = e^{i k a} ψ (x)`. -/
theorem bloch_theorem
    {a : ℝ} (ha : a ≠ 0) {H : (ℝ → ℂ) → (ℝ → ℂ)} {E : ℂ} {ψ : ℝ → ℂ}
    (hH : CommutesWithTranslation a H)
    (hEig : H ψ = fun x => E * ψ x)
    (hsimple : ∀ φ : ℝ → ℂ, (H φ = fun x => E * φ x) → ∃ c : ℂ, ∀ x, φ x = c * ψ x)
    (hnorm : ∀ x, ‖ψ (x + a)‖ = ‖ψ x‖)
    (hne : ∃ x₀, ψ x₀ ≠ 0) :
    ∃ (k : ℝ) (u : ℝ → ℂ),
      (∀ x, u (x + a) = u x) ∧
      (∀ x, ψ x = Complex.exp (Complex.I * k * x) * u x) ∧
      (∀ x, ψ (x + a) = Complex.exp (Complex.I * k * a) * ψ x) := by
  obtain ⟨c, hc⟩ := translation_eigenvalue_of_simple_eigenstate hH hEig hsimple
  obtain ⟨x₀, hx₀⟩ := hne
  -- the translation eigenvalue has modulus one
  have hcnorm : ‖c‖ = 1 := by
    have h1 : ‖c‖ * ‖ψ x₀‖ = ‖ψ x₀‖ := by
      rw [← norm_mul, ← hc x₀, hnorm x₀]
    have h2 : ‖ψ x₀‖ ≠ 0 := by simpa using hx₀
    field_simp [h2] at h1
    exact h1
  obtain ⟨k, hk⟩ := exists_real_wavenumber hcnorm ha
  have hψ : ∀ x, ψ (x + a) = Complex.exp (Complex.I * k * a) * ψ x := by
    intro x; rw [hc x, hk]
  obtain ⟨u, hu, hfac⟩ := bloch_factorization hψ
  exact ⟨k, u, hu, hfac, hψ⟩

open Classical in
/-- An auxiliary Hamiltonian used to witness that the hypotheses of `Phys.bloch_theorem` are
non-vacuous: it acts as the identity on constant wave functions and adds `1` to every other
wave function, so its eigenvalue `1` is simple with eigenstate the constant function. -/
noncomputable def constantSelector : (ℝ → ℂ) → (ℝ → ℂ) :=
  fun φ => if (∃ c : ℂ, ∀ x, φ x = c) then φ else fun x => φ x + 1

/-- The hypotheses of `Phys.bloch_theorem` are satisfiable: there really is a Hamiltonian
commuting with a lattice translation, with a simple eigenvalue whose eigenstate is nonzero and
has translation-invariant modulus. -/
theorem bloch_theorem_hypotheses_satisfiable :
    ∃ (a : ℝ) (H : (ℝ → ℂ) → (ℝ → ℂ)) (E : ℂ) (ψ : ℝ → ℂ),
      a ≠ 0 ∧ CommutesWithTranslation a H ∧ (H ψ = fun x => E * ψ x) ∧
      (∀ φ : ℝ → ℂ, (H φ = fun x => E * φ x) → ∃ c : ℂ, ∀ x, φ x = c * ψ x) ∧
      (∀ x, ‖ψ (x + a)‖ = ‖ψ x‖) ∧ (∃ x₀, ψ x₀ ≠ 0) := by
  classical
  refine ⟨1, constantSelector, 1, fun _ => 1, one_ne_zero, ?_, ?_, ?_, ?_, ⟨0, one_ne_zero⟩⟩
  · intro φ
    have hiff : (∃ c : ℂ, ∀ x, translate 1 φ x = c) ↔ (∃ c : ℂ, ∀ x, φ x = c) := by
      constructor
      · rintro ⟨c, hc⟩
        refine ⟨c, fun x => ?_⟩
        have := hc (x - 1)
        simpa [translate] using this
      · rintro ⟨c, hc⟩
        exact ⟨c, fun x => hc _⟩
    by_cases h : (∃ c : ℂ, ∀ x, φ x = c)
    · simp [constantSelector, h, hiff.2 h]
    · simp only [constantSelector, if_neg h, if_neg (fun hh => h (hiff.1 hh))]
      rfl
  · simp [constantSelector]
  · intro φ hφ
    by_cases h : (∃ c : ℂ, ∀ x, φ x = c)
    · obtain ⟨c, hc⟩ := h
      exact ⟨c, by simp [hc]⟩
    · exfalso
      rw [constantSelector, if_neg h] at hφ
      have := congrFun hφ 0
      simp at this
  · intro x; simp

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

