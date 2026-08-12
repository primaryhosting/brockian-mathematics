/-
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
Statement: ⟨e^{−βW}⟩ = e^{−βΔF} for nonequilibrium work (Jarzynski).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
Statement: ⟨e^{−βW}⟩ = e^{−βΔF} for nonequilibrium work (Jarzynski).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

variable {Ω : Type*} [Fintype Ω]

/-- The canonical partition function `Z = ∑ₓ e^{−β H(x)}` of a Hamiltonian `H`
on a finite state space at inverse temperature `β`. -/
noncomputable def partition (beta : ℝ) (H : Ω → ℝ) : ℝ := ∑ x, Real.exp (-beta * H x)

/-- The equilibrium free energy `F = −β⁻¹ log Z`. -/
noncomputable def freeEnergy (beta : ℝ) (H : Ω → ℝ) : ℝ :=
  -(1 / beta) * Real.log (partition beta H)

lemma partition_pos [Nonempty Ω] (beta : ℝ) (H : Ω → ℝ) : 0 < partition beta H :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- **Jarzynski equality.**  A finite classical system is prepared in the Gibbs state of the
initial Hamiltonian `H₀` at inverse temperature `β`, and then driven by a deterministic,
measure-preserving (Liouville) dynamics `phi : Ω ≃ Ω` while the Hamiltonian is switched to `H₁`.
The work performed along the trajectory starting at `x` is `W(x) = H₁(phi x) − H₀(x)`.
Then the average of `e^{−βW}` over the initial Gibbs ensemble equals `e^{−βΔF}`, where
`ΔF = F₁ − F₀` is the equilibrium free-energy difference. -/
theorem jarzynski_equality [Nonempty Ω] (beta : ℝ) (hbeta : beta ≠ 0)
    (H0 H1 : Ω → ℝ) (phi : Ω ≃ Ω) :
    ∑ x, (Real.exp (-beta * H0 x) / partition beta H0) *
        Real.exp (-beta * (H1 (phi x) - H0 x))
      = Real.exp (-beta * (freeEnergy beta H1 - freeEnergy beta H0)) := by
  have hZ0 : 0 < partition beta H0 := partition_pos beta H0
  have hZ1 : 0 < partition beta H1 := partition_pos beta H1
  have hlhs : ∑ x, (Real.exp (-beta * H0 x) / partition beta H0) *
      Real.exp (-beta * (H1 (phi x) - H0 x))
      = (∑ x, Real.exp (-beta * H1 (phi x))) / partition beta H0 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [div_mul_eq_mul_div, ← Real.exp_add]
    ring_nf
  rw [hlhs, Equiv.sum_comp phi (fun y => Real.exp (-beta * H1 y))]
  have hF : -beta * (freeEnergy beta H1 - freeEnergy beta H0)
      = Real.log (partition beta H1) - Real.log (partition beta H0) := by
    unfold freeEnergy
    field_simp
    ring
  rw [hF, Real.exp_sub, Real.exp_log hZ1, Real.exp_log hZ0]
  rfl

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

