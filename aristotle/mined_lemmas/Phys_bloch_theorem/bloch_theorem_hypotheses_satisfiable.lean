/-
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Statement: Eigenstates of a periodic Hamiltonian are Bloch waves e^{ikx}u_k(x).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Phys

/-- Translation of a wave function by the lattice constant `a`: `(transl a f) x = f (x + a)`. -/

lemma bloch_theorem_hypotheses_satisfiable :
    ∃ (a : ℝ) (H : (ℝ → ℂ) → (ℝ → ℂ)) (ψ : ℝ → ℂ) (E : ℂ) (x₀ M : ℝ),
      0 < a ∧ PeriodicHamiltonian a H ∧ H ψ = E • ψ ∧
      (∀ g : ℝ → ℂ, H g = E • g → ∃ c : ℂ, g = c • ψ) ∧ ψ x₀ ≠ 0 ∧ (∀ x, ‖ψ x‖ ≤ M) := by
  classical
  set ψ : ℝ → ℂ := fun x => Complex.exp (x * Complex.I) with hψdef
  refine ⟨2 * Real.pi, fun f => if f = ψ then ψ else 0, ψ, 1, 0, 1, by positivity, ?_, ?_, ?_,
    ?_, ?_⟩
  · -- periodicity of the Hamiltonian
    have hψper : transl (2 * Real.pi) ψ = ψ := by
      funext x
      simp only [transl, hψdef]
      rw [show ((x + 2 * Real.pi : ℝ) : ℂ) * Complex.I
            = (x : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    intro f
    by_cases hf : f = ψ
    · subst hf
      simp [hψper]
    · have hf' : transl (2 * Real.pi) f ≠ ψ := by
        intro h
        exact hf (transl_injective (2 * Real.pi) (h.trans hψper.symm))
      simp only [hf, hf', if_false]
      funext x
      simp [transl]
  · simp
  · intro g hg
    by_cases hgψ : g = ψ
    · exact ⟨1, by simp [hgψ]⟩
    · refine ⟨0, ?_⟩
      simp only [hgψ, if_false, one_smul] at hg
      simp [← hg]
  · simp [hψdef]
  · intro x
    simp [hψdef, Complex.norm_exp_ofReal_mul_I]

end Phys

