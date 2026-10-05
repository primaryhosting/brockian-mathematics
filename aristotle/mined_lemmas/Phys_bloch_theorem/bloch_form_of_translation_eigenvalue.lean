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

set_option maxHeartbeats 1000000

namespace Phys

/-- `psi` is a (twice differentiable) solution of the time-independent one-dimensional
Schrödinger equation with potential `V` and energy `E`, in units where `ħ² / 2m = 1`:
`-ψ'' + V ψ = E ψ`, i.e. `ψ'' = (V - E) ψ`. -/
structure IsSchrodingerSolution (V : ℝ → ℂ) (E : ℂ) (psi : ℝ → ℂ) : Prop where
  differentiable : Differentiable ℝ psi
  differentiable_deriv : Differentiable ℝ (deriv psi)
  eqn : ∀ x : ℝ, deriv (deriv psi) x = (V x - E) * psi x

/-- If the potential is `a`-periodic, then translating a solution of the Schrödinger equation
by `a` gives again a solution with the same energy. -/

theorem bloch_form_of_translation_eigenvalue {psi : ℝ → ℂ} {a : ℝ} (ha : a ≠ 0) {lam : ℂ}
    (hnorm : ‖lam‖ = 1) (hlam : ∀ x, psi (x + a) = lam * psi x) :
    ∃ (k : ℝ) (u : ℝ → ℂ), (∀ x, u (x + a) = u x) ∧
      ∀ x, psi x = Complex.exp (Complex.I * (k * x)) * u x := by
  obtain ⟨θ, hlamexp⟩ : ∃ θ : ℝ, lam = Complex.exp (θ * Complex.I) := by
    refine ⟨Complex.arg lam, ?_⟩
    have h := Complex.norm_mul_exp_arg_mul_I lam
    rw [hnorm] at h
    simpa using h.symm
  refine ⟨θ / a, fun x => Complex.exp (-(Complex.I * ((θ / a : ℝ) * x))) * psi x, ?_, ?_⟩
  · intro x
    simp only
    rw [hlam x, hlamexp]
    have hka : ((θ / a : ℝ) : ℂ) * ((a : ℝ) : ℂ) = (θ : ℂ) := by
      have hac : ((a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
      push_cast
      field_simp
    have hexp : -(Complex.I * (((θ / a : ℝ) : ℂ) * ((x + a : ℝ) : ℂ)))
        = -(Complex.I * (((θ / a : ℝ) : ℂ) * ((x : ℝ) : ℂ)))
          - ((θ / a : ℝ) : ℂ) * ((a : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hexp, hka, Complex.exp_sub]
    have hne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  · intro x
    simp only
    rw [← mul_assoc, ← Complex.exp_add]
    simp

/-- **Bloch's theorem.**
Let `V` be a potential with period `a > 0`, and let `psi` be a bounded eigenstate of the
corresponding Hamiltonian `H = -d²/dx² + V` with energy `E`, not identically zero, and assume
the bounded eigenspace at energy `E` is nondegenerate (one dimensional).  Then `psi` is a Bloch
wave: there exist a real wave number `k` and an `a`-periodic function `u` such that
`psi x = e^{i k x} * u x` for all `x`. -/
