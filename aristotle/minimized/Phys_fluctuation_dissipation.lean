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

/-!
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

open Finset

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- Boltzmann weight of the state `w` for the perturbed Hamiltonian
`H - l • B` at inverse temperature `beta`. -/
noncomputable def weight (beta : ℝ) (H B : Ω → ℝ) (l : ℝ) (w : Ω) : ℝ :=
  Real.exp (-beta * (H w - l * B w))

/-- Partition function of the perturbed system. -/
noncomputable def partition (beta : ℝ) (H B : Ω → ℝ) (l : ℝ) : ℝ :=
  ∑ w, weight beta H B l w

/-- Equilibrium (canonical) expectation value of the observable `A` in the
system perturbed by `-l • B`. -/
noncomputable def avg (beta : ℝ) (H B : Ω → ℝ) (A : Ω → ℝ) (l : ℝ) : ℝ :=
  (∑ w, A w * weight beta H B l w) / partition beta H B l

lemma partition_pos (beta : ℝ) (H B : Ω → ℝ) (l : ℝ) : 0 < partition beta H B l := by
  refine Finset.sum_pos (fun w _ => Real.exp_pos _) ?_
  simpa using Finset.univ_nonempty (α := Ω)

lemma hasDerivAt_weight (beta : ℝ) (H B : Ω → ℝ) (w : Ω) :
    HasDerivAt (fun l => weight beta H B l w) (beta * B w * weight beta H B 0 w) 0 := by
  have h : HasDerivAt (fun l : ℝ => -beta * (H w - l * B w)) (beta * B w) 0 := by
    have : HasDerivAt (fun l : ℝ => -beta * (H w - l * B w))
        (-beta * (0 - 1 * B w)) 0 := by
      have h1 : HasDerivAt (fun l : ℝ => l * B w) (1 * B w) 0 :=
        (hasDerivAt_id (0 : ℝ)).mul_const _
      simpa using ((hasDerivAt_const (0 : ℝ) (H w)).sub h1).const_mul (-beta)
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  simpa [weight, mul_comm, mul_left_comm, mul_assoc] using h.exp

/-- **Static fluctuation–dissipation theorem** (classical, finite state space).

For a finite classical system with Hamiltonian `H` at inverse temperature `beta`,
perturbed to `H - l • B`, the linear response of the equilibrium average of an
observable `A` to the perturbation strength `l` equals `beta` times the
equilibrium covariance (connected correlation function) of `A` and `B`:

`d⟨A⟩/dl |_{l=0} = beta * (⟨A B⟩ - ⟨A⟩⟨B⟩)`. -/
theorem fluctuation_dissipation (beta : ℝ) (H A B : Ω → ℝ) :
    HasDerivAt (avg beta H B A)
      (beta * (avg beta H B (fun w => A w * B w) 0
        - avg beta H B A 0 * avg beta H B B 0)) 0 := by
  set Z : ℝ := partition beta H B 0 with hZdef
  have hZ : Z ≠ 0 := ne_of_gt (partition_pos beta H B 0)
  have hN : HasDerivAt (fun l => ∑ w, A w * weight beta H B l w)
      (∑ w, A w * (beta * B w * weight beta H B 0 w)) 0 :=
    HasDerivAt.sum (fun w _ => ((hasDerivAt_weight beta H B w).const_mul (A w)))
  have hD : HasDerivAt (partition beta H B)
      (∑ w, beta * B w * weight beta H B 0 w) 0 :=
    HasDerivAt.sum (fun w _ => hasDerivAt_weight beta H B w)
  have := hN.div hD hZ
  convert this using 1
  have hAB : ∑ w, A w * (beta * B w * weight beta H B 0 w)
      = beta * ∑ w, (A w * B w) * weight beta H B 0 w := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring
  have hB : ∑ w, beta * B w * weight beta H B 0 w
      = beta * ∑ w, B w * weight beta H B 0 w := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring
  rw [hAB, hB]
  simp only [avg, ← hZdef]
  field_simp
  ring

end Phys

