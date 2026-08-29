/-
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Phys

open Finset

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- Canonical partition function `Z = ∑ₓ e^{-β H(x)}` of a finite classical system. -/
noncomputable def partitionFunction (beta : ℝ) (H : Ω → ℝ) : ℝ :=
  ∑ x, Real.exp (-beta * H x)

lemma partitionFunction_pos (beta : ℝ) (H : Ω → ℝ) :
    0 < partitionFunction (Ω := Ω) beta H :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- Gibbs (canonical equilibrium) probability of the microstate `x`. -/
noncomputable def gibbs (beta : ℝ) (H : Ω → ℝ) (x : Ω) : ℝ :=
  Real.exp (-beta * H x) / partitionFunction beta H

/-- The work performed along the (deterministic, Liouville-measure-preserving) trajectory
starting at `x`: the final energy minus the initial energy. -/
noncomputable def work (H₀ H₁ : Ω → ℝ) (phi : Equiv.Perm Ω) (x : Ω) : ℝ :=
  H₁ (phi x) - H₀ x

/-- Free-energy difference between the final and initial equilibrium ensembles,
`ΔF = -(1/β) log (Z₁ / Z₀)`. -/
noncomputable def freeEnergyDiff (beta : ℝ) (H₀ H₁ : Ω → ℝ) : ℝ :=
  -(1 / beta) * Real.log (partitionFunction (Ω := Ω) beta H₁ / partitionFunction (Ω := Ω) beta H₀)

/-- **Jarzynski equality.**  For a finite classical system initially in the Gibbs state of `H₀`
at inverse temperature `β ≠ 0`, driven by a measure-preserving (Liouville) evolution `phi`
to a final energy function `H₁`, the equilibrium average of `e^{-βW}` over initial microstates
equals `e^{-βΔF}`, where `ΔF` is the free-energy difference of the two equilibrium ensembles. -/
theorem jarzynski_equality (beta : ℝ) (hbeta : beta ≠ 0) (H₀ H₁ : Ω → ℝ) (phi : Equiv.Perm Ω) :
    ∑ x, gibbs beta H₀ x * Real.exp (-beta * work H₀ H₁ phi x)
      = Real.exp (-beta * freeEnergyDiff (Ω := Ω) beta H₀ H₁) := by
  have h0 : (0:ℝ) < partitionFunction (Ω := Ω) beta H₀ := partitionFunction_pos beta H₀
  have h1 : (0:ℝ) < partitionFunction (Ω := Ω) beta H₁ := partitionFunction_pos beta H₁
  have hratio : (0:ℝ) < partitionFunction (Ω := Ω) beta H₁ / partitionFunction (Ω := Ω) beta H₀ :=
    div_pos h1 h0
  have hrhs : Real.exp (-beta * freeEnergyDiff (Ω := Ω) beta H₀ H₁)
      = partitionFunction (Ω := Ω) beta H₁ / partitionFunction (Ω := Ω) beta H₀ := by
    unfold freeEnergyDiff
    rw [show -beta * (-(1 / beta) *
        Real.log (partitionFunction (Ω := Ω) beta H₁ / partitionFunction (Ω := Ω) beta H₀))
      = Real.log (partitionFunction (Ω := Ω) beta H₁ / partitionFunction (Ω := Ω) beta H₀) by
        field_simp]
    exact Real.exp_log hratio
  rw [hrhs]
  have hterm : ∀ x : Ω, gibbs beta H₀ x * Real.exp (-beta * work H₀ H₁ phi x)
      = Real.exp (-beta * H₁ (phi x)) / partitionFunction (Ω := Ω) beta H₀ := by
    intro x
    unfold gibbs work
    rw [div_mul_eq_mul_div, ← Real.exp_add]
    ring_nf
  rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.sum_div]
  congr 1
  exact Fintype.sum_equiv phi _ _ (fun x => rfl)

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

