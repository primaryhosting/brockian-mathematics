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

namespace Phys

/-- The translation operator `T_a` acting on wavefunctions: `(T_a ψ)(x) = ψ (x + a)`. -/
def translate (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := fun x => f (x + a)

/-- A wavefunction `ψ` is a *Bloch wave* with lattice constant `a` and quasimomentum `k`
if it has the form `ψ (x) = e^{i k x} u (x)` with `u` periodic of period `a`. -/
def IsBlochWave (a k : ℝ) (ψ : ℝ → ℂ) : Prop :=
  ∃ u : ℝ → ℂ, Function.Periodic u a ∧
    ∀ x : ℝ, ψ x = Complex.exp (k * x * Complex.I) * u x

/-- Iterating the quasi-periodicity relation `ψ (x + a) = lam * ψ x`. -/
lemma iterate_translate_eq {a : ℝ} {ψ : ℝ → ℂ} {lam : ℂ}
    (hT : ∀ x : ℝ, ψ (x + a) = lam * ψ x) :
    ∀ (n : ℕ) (x : ℝ), ψ (x + n * a) = lam ^ n * ψ x := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
      intro x
      have hx : x + (↑(n + 1) : ℝ) * a = (x + n * a) + a := by push_cast; ring
      rw [hx, hT, ih, pow_succ]
      ring

/-- If `ψ` is bounded, not identically zero at `x₀`, and satisfies `ψ (x + a) = lam * ψ x`,
then `‖lam‖ ≤ 1`. -/
lemma norm_le_one_of_bounded {a : ℝ} {ψ : ℝ → ℂ} {lam : ℂ} {C x₀ : ℝ}
    (hT : ∀ x : ℝ, ψ (x + a) = lam * ψ x)
    (hb : ∀ x : ℝ, ‖ψ x‖ ≤ C) (hx₀ : ψ x₀ ≠ 0) :
    ‖lam‖ ≤ 1 := by
  by_contra h
  push_neg at h
  have hpos : 0 < ‖ψ x₀‖ := norm_pos_iff.mpr hx₀
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / ‖ψ x₀‖) h
  have hle := hb (x₀ + n * a)
  rw [iterate_translate_eq hT n x₀, norm_mul, norm_pow] at hle
  rw [div_lt_iff₀ hpos] at hn
  linarith

/-- A bounded, nonzero quasi-periodic wavefunction forces the phase factor to have modulus one. -/
lemma norm_eq_one_of_bounded {a : ℝ} {ψ : ℝ → ℂ} {lam : ℂ} {C x₀ : ℝ}
    (hT : ∀ x : ℝ, ψ (x + a) = lam * ψ x)
    (hb : ∀ x : ℝ, ‖ψ x‖ ≤ C) (hx₀ : ψ x₀ ≠ 0) :
    ‖lam‖ = 1 := by
  have hlam : lam ≠ 0 := by
    intro h
    apply hx₀
    have hxa := hT (x₀ - a)
    rw [h] at hxa
    simpa using hxa
  have h1 : ‖lam‖ ≤ 1 := norm_le_one_of_bounded hT hb hx₀
  have hT' : ∀ x : ℝ, (fun y : ℝ => ψ (-y)) (x + a) = lam⁻¹ * (fun y : ℝ => ψ (-y)) x := by
    intro x
    have h := hT (-(x + a))
    show ψ (-(x + a)) = lam⁻¹ * ψ (-x)
    have hx : -(x + a) + a = -x := by ring
    rw [hx] at h
    field_simp
    rw [h]
    ring
  have h2 : ‖lam⁻¹‖ ≤ 1 :=
    norm_le_one_of_bounded (C := C) (x₀ := -x₀) hT' (fun x => hb (-x)) (by simpa using hx₀)
  rw [norm_inv] at h2
  have hpos : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
  rw [inv_le_one_iff₀] at h2
  rcases h2 with h | h
  · linarith
  · linarith

/-- If `ψ (x + a) = e^{i θ} ψ (x)` with `a ≠ 0`, then `ψ` is a Bloch wave with
quasimomentum `k = θ / a`. -/
lemma isBlochWave_of_quasiperiodic {a θ : ℝ} (ha : a ≠ 0) {ψ : ℝ → ℂ}
    (hT : ∀ x : ℝ, ψ (x + a) = Complex.exp (θ * Complex.I) * ψ x) :
    IsBlochWave a (θ / a) ψ := by
  refine ⟨fun x => Complex.exp (-((θ / a : ℝ) * x * Complex.I)) * ψ x, ?_, ?_⟩
  · intro x
    show Complex.exp (-((θ / a : ℝ) * ((x + a : ℝ) : ℂ) * Complex.I)) * ψ (x + a)
      = Complex.exp (-((θ / a : ℝ) * (x : ℂ) * Complex.I)) * ψ x
    rw [hT x]
    have hka : ((θ / a : ℝ) : ℂ) * ((x + a : ℝ) : ℂ) = ((θ / a : ℝ) : ℂ) * (x : ℂ) + (θ : ℂ) := by
      have hac : ((a : ℂ)) ≠ 0 := by exact_mod_cast ha
      push_cast
      field_simp
    rw [hka]
    rw [show -((((θ / a : ℝ) : ℂ) * (x : ℂ) + (θ : ℂ)) * Complex.I)
        = -(((θ / a : ℝ) : ℂ) * (x : ℂ) * Complex.I) + (-(θ : ℂ) * Complex.I) by ring]
    rw [Complex.exp_add]
    rw [show (-(θ : ℂ) * Complex.I) = -((θ : ℂ) * Complex.I) by ring, Complex.exp_neg]
    field_simp
    rw [← Complex.exp_add]
    simp
  · intro x
    rw [← mul_assoc, ← Complex.exp_add]
    simp

/-- **Bloch's theorem.**  Let `H` be a Hamiltonian acting on wavefunctions on the line which
is invariant under translation by the lattice constant `a > 0`, i.e. it commutes with the
translation operator `T_a`.  Let `ψ` be a bounded eigenstate of `H` with a nondegenerate
eigenvalue `E` (every eigenfunction for `E` is a scalar multiple of `ψ`), and `ψ ≠ 0`.

Then `ψ` is a Bloch wave: there is a quasimomentum `k` and an `a`-periodic function `u`
with `ψ (x) = e^{i k x} u (x)` for all `x`. -/
theorem bloch_theorem {a : ℝ} (ha : 0 < a) (H : (ℝ → ℂ) → (ℝ → ℂ))
    (hcomm : ∀ f : ℝ → ℂ, H (translate a f) = translate a (H f))
    (ψ : ℝ → ℂ) (E : ℂ) (hEig : H ψ = E • ψ) (hψ : ψ ≠ 0)
    (hnd : ∀ g : ℝ → ℂ, H g = E • g → ∃ c : ℂ, g = c • ψ)
    (hbdd : ∃ C : ℝ, ∀ x : ℝ, ‖ψ x‖ ≤ C) :
    ∃ k : ℝ, IsBlochWave a k ψ := by
  obtain ⟨C, hC⟩ := hbdd
  have hTeig : H (translate a ψ) = E • translate a ψ := by
    rw [hcomm ψ, hEig]
    rfl
  obtain ⟨c, hc⟩ := hnd _ hTeig
  have hT : ∀ x : ℝ, ψ (x + a) = c * ψ x := by
    intro x
    have h := congrFun hc x
    simpa [translate] using h
  obtain ⟨x₀, hx₀⟩ : ∃ x : ℝ, ψ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hψ (funext h)
  have hnorm := norm_eq_one_of_bounded hT hC hx₀
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff c).mp hnorm
  exact ⟨θ / a, isBlochWave_of_quasiperiodic ha.ne' (by rw [hθ]; exact hT)⟩

end Phys

