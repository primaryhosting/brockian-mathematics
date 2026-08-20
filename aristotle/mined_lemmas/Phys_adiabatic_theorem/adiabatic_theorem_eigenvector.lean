/-
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Phys

open Set

/-- **Uniqueness for a linear ODE in a Banach algebra.**
If `X : ℝ → F` solves the linear differential equation `X' t = A t * X t` with continuous
coefficient `A` and vanishing initial datum, then `X` vanishes identically. -/

theorem adiabatic_theorem_eigenvector
    (H P dP : ℝ → (E →L[ℂ] E)) (e : ℝ → ℂ) (U : ℝ → (E →L[ℂ] E)) (ε : ℝ) (ψ₀ : E)
    (v : ℝ → E)
    (hH : Continuous H) (hdP : Continuous dP)
    (hP : ∀ s, HasDerivAt P (dP s) s)
    (hproj : ∀ s, P s * P s = P s)
    (heig : ∀ s, H s * P s = e s • P s)
    (heig' : ∀ s, P s * H s = e s • P s)
    (hnondeg : ∀ s, v s ≠ 0 ∧ LinearMap.range (P s).toLinearMap = Submodule.span ℂ {v s})
    (hε : 0 < ε)
    (hU0 : U 0 = 1)
    (hU : ∀ s, HasDerivAt U
      (((-(Complex.I / ε)) • H s + (dP s * P s - P s * dP s)) * U s) s)
    (hψ₀ : P 0 ψ₀ = ψ₀) :
    ∀ s, ∃ z : ℂ, U s ψ₀ = z • v s := by
  intro s
  have hmain := adiabatic_theorem H P dP e U ε ψ₀ hH hdP hP hproj heig heig'
    (fun s => ⟨v s, (hnondeg s).1, (hnondeg s).2⟩) hε hU0 hU hψ₀ s
  have hmem : U s ψ₀ ∈ LinearMap.range (P s).toLinearMap := ⟨U s ψ₀, hmain.1⟩
  rw [(hnondeg s).2, Submodule.mem_span_singleton] at hmem
  obtain ⟨z, hz⟩ := hmem
  exact ⟨z, hz.symm⟩

end

/-- A consistency (non-vacuity) check: the hypotheses of `Phys.adiabatic_theorem_eigenvector`
are satisfiable, here by the one-dimensional system with vanishing Hamiltonian. -/
example : ∀ s : ℝ, ∃ z : ℂ, (fun _ : ℝ => (1 : ℂ →L[ℂ] ℂ)) s (1 : ℂ) = z • (fun _ : ℝ => (1 : ℂ)) s := by
  refine adiabatic_theorem_eigenvector (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ => 0)
    (fun _ => 1) 1 1 (fun _ => 1) continuous_const continuous_const
    (fun s => hasDerivAt_const s _) (fun s => by simp) (fun s => by simp) (fun s => by simp)
    (fun s => ⟨one_ne_zero, ?_⟩) one_pos rfl
    (fun s => by simpa using hasDerivAt_const s (1 : ℂ →L[ℂ] ℂ)) (by simp)
  exact le_antisymm (fun x _ => Submodule.mem_span_singleton.mpr ⟨x, by simp⟩)
    (fun x _ => ⟨x, by simp⟩)

end Phys

