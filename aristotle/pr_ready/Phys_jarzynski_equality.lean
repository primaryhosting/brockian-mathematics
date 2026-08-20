/-!
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
Statement: ⟨e^{−βW}⟩ = e^{−βΔF} for nonequilibrium work (Jarzynski).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

open Finset

variable {X : Type*} [Fintype X] [Nonempty X]

/-- The canonical partition function `Z(β, H) = ∑ₓ e^{−β H(x)}` of a Hamiltonian `H`
on a finite phase space `X` at inverse temperature `β`. -/
noncomputable def partitionFunction (beta : ℝ) (H : X → ℝ) : ℝ :=
  ∑ x : X, Real.exp (-beta * H x)

/-- The Helmholtz free energy `F = −(1/β) log Z`. -/
noncomputable def freeEnergy (beta : ℝ) (H : X → ℝ) : ℝ :=
  -(1 / beta) * Real.log (partitionFunction beta H)

/-- The equilibrium (Boltzmann–Gibbs) probability of the state `x`. -/
noncomputable def gibbs (beta : ℝ) (H : X → ℝ) (x : X) : ℝ :=
  Real.exp (-beta * H x) / partitionFunction beta H

/-- The work performed along the trajectory starting at `x`, where the (Liouville,
i.e. measure preserving) protocol carries `x` to `T x` while the Hamiltonian is
switched from `H₀` to `H₁`. -/
def work (H0 H1 : X → ℝ) (T : Equiv.Perm X) (x : X) : ℝ := H1 (T x) - H0 x

lemma partitionFunction_pos (beta : ℝ) (H : X → ℝ) : 0 < partitionFunction beta H := by
  refine Finset.sum_pos (fun x _ => Real.exp_pos _) ?_
  exact Finset.univ_nonempty

/-- **Jarzynski equality.**  For a finite phase space, a system started in the Boltzmann
distribution of `H₀` and driven by an arbitrary phase-space bijection `T` (Liouville's
theorem) while the Hamiltonian is switched from `H₀` to `H₁`, the exponential average of
the work equals `e^{−β ΔF}`, where `ΔF = F(H₁) − F(H₀)` is the equilibrium free energy
difference. -/
theorem jarzynski_equality (beta : ℝ) (hbeta : beta ≠ 0) (H0 H1 : X → ℝ) (T : Equiv.Perm X) :
    ∑ x : X, gibbs beta H0 x * Real.exp (-beta * work H0 H1 T x)
      = Real.exp (-beta * (freeEnergy beta H1 - freeEnergy beta H0)) := by
  have h0 : (0:ℝ) < partitionFunction beta H0 := partitionFunction_pos beta H0
  have h1 : (0:ℝ) < partitionFunction beta H1 := partitionFunction_pos beta H1
  have hlhs : ∑ x : X, gibbs beta H0 x * Real.exp (-beta * work H0 H1 T x)
      = partitionFunction beta H1 / partitionFunction beta H0 := by
    rw [partitionFunction, Finset.sum_div]
    rw [← Equiv.sum_comp T (fun y => Real.exp (-beta * H1 y) / partitionFunction beta H0)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    unfold gibbs work
    rw [div_mul_eq_mul_div, ← Real.exp_add]
    ring_nf
  rw [hlhs, freeEnergy, freeEnergy]
  have : -beta * (-(1 / beta) * Real.log (partitionFunction beta H1)
      - -(1 / beta) * Real.log (partitionFunction beta H0))
      = Real.log (partitionFunction beta H1) - Real.log (partitionFunction beta H0) := by
    field_simp
    ring
  rw [this, Real.exp_sub, Real.exp_log h1, Real.exp_log h0]

end Phys

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

