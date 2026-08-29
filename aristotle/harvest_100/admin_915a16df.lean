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

variable {ι : Type*} [Fintype ι]

/-- Canonical partition function at inverse temperature `β` for energy function `E`. -/
noncomputable def partitionFunction (beta : ℝ) (E : ι → ℝ) : ℝ :=
  ∑ i, Real.exp (-beta * E i)

/-- Helmholtz free energy `F = -(1/β) log Z`. -/
noncomputable def freeEnergy (beta : ℝ) (E : ι → ℝ) : ℝ :=
  -(Real.log (partitionFunction beta E)) / beta

lemma partitionFunction_pos [Nonempty ι] (beta : ℝ) (E : ι → ℝ) :
    0 < partitionFunction beta E := by
  refine Finset.sum_pos (fun i _ => Real.exp_pos _) ?_
  simp

/-- **Jarzynski equality.**

Setting: a finite classical system with initial energy function `EA` and final energy function
`EB`, driven at inverse temperature `beta ≠ 0`.  The system starts in the equilibrium (Boltzmann)
distribution `p i = exp (-β * EA i) / Z_A`, and the driving protocol acts on phase space by a
measure-preserving (Liouville) bijection `tau`, so that the work performed along the trajectory
starting at `i` is `W i = EB (tau i) - EA i`.

Then the exponential average of the work equals the exponential of the free-energy difference:
`⟨e^{-βW}⟩ = e^{-βΔF}` with `ΔF = F_B - F_A`. -/
theorem jarzynski_equality [Nonempty ι] (beta : ℝ) (hbeta : beta ≠ 0)
    (EA EB : ι → ℝ) (tau : ι ≃ ι) :
    ∑ i, (Real.exp (-beta * EA i) / partitionFunction beta EA) *
        Real.exp (-beta * (EB (tau i) - EA i))
      = Real.exp (-beta * (freeEnergy beta EB - freeEnergy beta EA)) := by
  have hZA : 0 < partitionFunction beta EA := partitionFunction_pos beta EA
  have hZB : 0 < partitionFunction beta EB := partitionFunction_pos beta EB
  have hlhs : ∑ i, (Real.exp (-beta * EA i) / partitionFunction beta EA) *
      Real.exp (-beta * (EB (tau i) - EA i))
      = partitionFunction beta EB / partitionFunction beta EA := by
    rw [eq_div_iff hZA.ne', Finset.sum_mul]
    have : ∀ i : ι, (Real.exp (-beta * EA i) / partitionFunction beta EA) *
        Real.exp (-beta * (EB (tau i) - EA i)) * partitionFunction beta EA
        = Real.exp (-beta * EB (tau i)) := by
      intro i
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hZA.ne', ← Real.exp_add]
      ring_nf
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    exact Fintype.sum_equiv tau _ _ (fun i => rfl)
  rw [hlhs, freeEnergy, freeEnergy]
  rw [show -beta * (-(Real.log (partitionFunction beta EB)) / beta -
      -(Real.log (partitionFunction beta EA)) / beta)
      = Real.log (partitionFunction beta EB) - Real.log (partitionFunction beta EA) by
    field_simp; ring]
  rw [Real.exp_sub, Real.exp_log hZB, Real.exp_log hZA]

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

