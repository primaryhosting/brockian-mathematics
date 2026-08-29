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

theorem schrodinger_shift {V : ℝ → ℂ} {E : ℂ} {psi : ℝ → ℂ} {a : ℝ}
    (hVper : ∀ x, V (x + a) = V x) (h : IsSchrodingerSolution V E psi) :
    IsSchrodingerSolution V E (fun x => psi (x + a)) := by
  have hd : (deriv fun x : ℝ => psi (x + a)) = fun x : ℝ => deriv psi (x + a) :=
    funext fun y => deriv_comp_add_const psi a y
  refine ⟨fun x => (h.differentiable (x + a)).comp x ((differentiable_id.add_const a) x), ?_, ?_⟩
  · rw [hd]
    exact fun x => (h.differentiable_deriv (x + a)).comp x ((differentiable_id.add_const a) x)
  · intro x
    rw [hd, deriv_comp_add_const (fun y => deriv psi y) a x, h.eqn (x + a), hVper x]

/-- A translation eigenvalue of a bounded function that does not vanish identically has
modulus one. -/
