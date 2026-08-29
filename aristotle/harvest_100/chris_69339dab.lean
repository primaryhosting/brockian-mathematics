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

/-- The translation operator by `a` acting on wave functions. -/
def translate (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := fun x => f (x + a)

/-- The one-dimensional Schrödinger Hamiltonian `H ψ = -ψ'' + V ψ`. -/
noncomputable def hamiltonian (V ψ : ℝ → ℂ) : ℝ → ℂ :=
  fun x => -deriv (deriv ψ) x + V x * ψ x

/-- If the potential is `a`-periodic, the Hamiltonian commutes with translation by `a`:
this is the structural input of Bloch's theorem, which lets one diagonalize `H` and the
translation operator simultaneously. -/
theorem hamiltonian_comm_translate (a : ℝ) (V : ℝ → ℂ) (hV : ∀ x, V (x + a) = V x)
    (ψ : ℝ → ℂ) :
    hamiltonian V (translate a ψ) = translate a (hamiltonian V ψ) := by
  have h1 : deriv (translate a ψ) = translate a (deriv ψ) := by
    funext x
    simpa [translate] using deriv_comp_add_const ψ a x
  have h2 : deriv (deriv (translate a ψ)) = translate a (deriv (deriv ψ)) := by
    funext x
    rw [h1]
    simpa [translate] using deriv_comp_add_const (deriv ψ) a x
  funext x
  simp only [hamiltonian, translate, h2, hV x]

/-- Iterating the translation eigenvalue equation: `ψ (x + n * a) = c ^ n * ψ x`. -/
theorem translate_iterate (a : ℝ) (ψ : ℝ → ℂ) (c : ℂ)
    (hψ : ∀ x, translate a ψ x = c * ψ x) (x : ℝ) :
    ∀ n : ℕ, ψ (x + n * a) = c ^ n * ψ x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have : ψ (x + n * a + a) = c * ψ (x + n * a) := hψ _
      have hx : x + (n + 1 : ℕ) * a = x + n * a + a := by push_cast; ring
      rw [hx, this, ih]
      ring

/-- A bounded, not identically vanishing eigenfunction of the translation operator has an
eigenvalue of unit modulus.  This is the physical input that turns the eigenvalue into a
phase `e ^ (i k a)`. -/
theorem translate_eigenvalue_norm_eq_one (a : ℝ) (ψ : ℝ → ℂ) (c : ℂ) (M : ℝ)
    (hbdd : ∀ x, ‖ψ x‖ ≤ M) (x₀ : ℝ) (hx₀ : ψ x₀ ≠ 0)
    (hψ : ∀ x, translate a ψ x = c * ψ x) : ‖c‖ = 1 := by
  have hpos : 0 < ‖ψ x₀‖ := norm_pos_iff.mpr hx₀
  have hM : 0 < M := lt_of_lt_of_le hpos (hbdd x₀)
  have key : ∀ n : ℕ, ‖c‖ ^ n * ‖ψ x₀‖ ≤ M := by
    intro n
    have := translate_iterate a ψ c hψ x₀ n
    have h2 : ‖ψ (x₀ + n * a)‖ = ‖c‖ ^ n * ‖ψ x₀‖ := by
      rw [this]; simp
    rw [← h2]
    exact hbdd _
  have hle : ‖c‖ ≤ 1 := by
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / ‖ψ x₀‖) h
    have := key n
    rw [div_lt_iff₀ hpos] at hn
    linarith
  have hge : 1 ≤ ‖c‖ := by
    by_contra h
    push_neg at h
    -- going backwards along the lattice, `ψ` would blow up
    have back : ∀ n : ℕ, ‖ψ x₀‖ ≤ ‖c‖ ^ n * M := by
      intro n
      have hstep := translate_iterate a ψ c hψ (x₀ - n * a) n
      have hx : x₀ - n * a + n * a = x₀ := by ring
      rw [hx] at hstep
      have : ‖ψ x₀‖ = ‖c‖ ^ n * ‖ψ (x₀ - n * a)‖ := by
        rw [hstep]; simp
      rw [this]
      have hc0 : (0 : ℝ) ≤ ‖c‖ ^ n := by positivity
      exact mul_le_mul_of_nonneg_left (hbdd _) hc0
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := ‖ψ x₀‖ / M) (y := ‖c‖) (by positivity) h
    have := back n
    rw [lt_div_iff₀ hM] at hn
    linarith
  linarith

/-- **Bloch's theorem.**  If a wave function `ψ` is an eigenfunction of the translation
operator by the lattice constant `a` (which happens for eigenstates of a Hamiltonian with an
`a`-periodic potential, see `Phys.hamiltonian_comm_translate`), with an eigenvalue `c` of unit
modulus, then `ψ` is a Bloch wave: there are a crystal momentum `k : ℝ` and an `a`-periodic
function `u` with `ψ x = e ^ (i k x) * u x` for all `x`. -/
theorem bloch_theorem (a : ℝ) (ha : 0 < a) (ψ : ℝ → ℂ) (c : ℂ) (hc : ‖c‖ = 1)
    (hψ : ∀ x, translate a ψ x = c * ψ x) :
    ∃ k : ℝ, ∃ u : ℝ → ℂ, (∀ x, u (x + a) = u x) ∧
      ∀ x, ψ x = Complex.exp (Complex.I * k * x) * u x := by
  have hcexp : Complex.exp (Complex.arg c * Complex.I) = c := by
    have := Complex.norm_mul_exp_arg_mul_I c
    rw [hc] at this
    simpa using this
  refine ⟨Complex.arg c / a, fun x => Complex.exp (-(Complex.I * (Complex.arg c / a) * x)) * ψ x,
    ?_, ?_⟩
  · intro x
    have hx : ψ (x + a) = c * ψ x := hψ x
    have hane : (a : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt ha
    have hsplit : -(Complex.I * ((Complex.arg c : ℂ) / a) * ((x : ℂ) + a))
        = -(Complex.I * ((Complex.arg c : ℂ) / a) * x) + -((Complex.arg c : ℂ) * Complex.I) := by
      field_simp
      ring
    rw [show ((x : ℝ) + a : ℝ) = (x + a : ℝ) from rfl]
    push_cast
    rw [hx, hsplit, Complex.exp_add]
    rw [show Complex.exp (-((Complex.arg c : ℂ) * Complex.I))
        = (Complex.exp ((Complex.arg c : ℂ) * Complex.I))⁻¹ by
      rw [← Complex.exp_neg]]
    rw [hcexp]
    have hc0 : c ≠ 0 := by
      intro h
      rw [h] at hc
      simp at hc
    field_simp
  · intro x
    rw [← mul_assoc, ← Complex.exp_add]
    simp

/-- Bloch's theorem for a bounded, nonzero eigenfunction of the lattice translation: no
assumption on the eigenvalue `c` is needed, its unit modulus is forced by boundedness. -/
theorem bloch_theorem_of_bounded (a : ℝ) (ha : 0 < a) (ψ : ℝ → ℂ) (c : ℂ) (M : ℝ)
    (hbdd : ∀ x, ‖ψ x‖ ≤ M) (x₀ : ℝ) (hx₀ : ψ x₀ ≠ 0)
    (hψ : ∀ x, translate a ψ x = c * ψ x) :
    ∃ k : ℝ, ∃ u : ℝ → ℂ, (∀ x, u (x + a) = u x) ∧
      ∀ x, ψ x = Complex.exp (Complex.I * k * x) * u x :=
  bloch_theorem a ha ψ c (translate_eigenvalue_norm_eq_one a ψ c M hbdd x₀ hx₀ hψ) hψ

/-- A Bloch wave is automatically an eigenfunction of the lattice translation, with
eigenvalue the phase `e ^ (i k a)`; together with `Phys.bloch_theorem` this characterizes
Bloch waves among wave functions. -/
theorem translate_eigen_of_bloch (a k : ℝ) (ψ u : ℝ → ℂ) (hu : ∀ x, u (x + a) = u x)
    (hψ : ∀ x, ψ x = Complex.exp (Complex.I * k * x) * u x) :
    ∀ x, translate a ψ x = Complex.exp (Complex.I * k * a) * ψ x := by
  intro x
  simp only [translate, hψ, hu x]
  push_cast
  rw [← mul_assoc, ← Complex.exp_add]
  ring_nf

/-- **Bloch's theorem for a periodic Hamiltonian.**  Let `V` be `a`-periodic and let `ψ` be a
bounded, nonzero eigenfunction of `H = -d²/dx² + V` with eigenvalue `E`, whose eigenspace is
one-dimensional (spanned by `ψ`).  Then `ψ` is a Bloch wave `e ^ (i k x) * u x` with `u`
`a`-periodic. -/
theorem bloch_theorem_of_periodic_hamiltonian (a : ℝ) (ha : 0 < a) (V ψ : ℝ → ℂ) (E : ℂ)
    (M : ℝ) (hV : ∀ x, V (x + a) = V x)
    (hE : ∀ x, hamiltonian V ψ x = E * ψ x)
    (hnd : ∀ φ : ℝ → ℂ, (∀ x, hamiltonian V φ x = E * φ x) → ∃ c : ℂ, ∀ x, φ x = c * ψ x)
    (hbdd : ∀ x, ‖ψ x‖ ≤ M) (x₀ : ℝ) (hx₀ : ψ x₀ ≠ 0) :
    ∃ k : ℝ, ∃ u : ℝ → ℂ, (∀ x, u (x + a) = u x) ∧
      ∀ x, ψ x = Complex.exp (Complex.I * k * x) * u x := by
  have hcomm := hamiltonian_comm_translate a V hV ψ
  have hTE : ∀ x, hamiltonian V (translate a ψ) x = E * translate a ψ x := by
    intro x
    rw [hcomm]
    simpa [translate] using hE (x + a)
  obtain ⟨c, hc⟩ := hnd (translate a ψ) hTE
  exact bloch_theorem_of_bounded a ha ψ c M hbdd x₀ hx₀ hc

#print axioms bloch_theorem
#print axioms bloch_theorem_of_periodic_hamiltonian

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

