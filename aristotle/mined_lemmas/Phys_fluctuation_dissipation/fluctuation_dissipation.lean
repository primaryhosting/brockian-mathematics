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

import Mathlib

/-!
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Statement: The FDT relates linear response to equilibrium correlations.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

variable {Ω : Type*} [Fintype Ω]

/-- Boltzmann weight of the state `w` at inverse temperature `beta` for the
Hamiltonian `E - f • A`, i.e. the unperturbed energy `E` perturbed by an external
field `f` coupled to the observable `A`. -/

theorem fluctuation_dissipation [Nonempty Ω] (beta : ℝ) (E A B : Ω → ℝ) (f : ℝ) :
    HasDerivAt (fun f => expect beta E A f B)
      (beta * (expect beta E A f (fun w => A w * B w)
        - expect beta E A f A * expect beta E A f B)) f := by
  have hZ := partition_pos (Ω := Ω) beta E A f
  have hnum := hasDerivAt_weighted_sum beta E A B f
  have hden := hasDerivAt_partition beta E A f
  have h := hnum.div hden hZ.ne'
  have key : ((∑ w, beta * (A w * B w) * weight beta E A f w) * partition beta E A f
      - (∑ w, B w * weight beta E A f w) * (∑ w, beta * A w * weight beta E A f w))
        / partition beta E A f ^ 2
      = beta * (expect beta E A f (fun w => A w * B w)
        - expect beta E A f A * expect beta E A f B) := by
    have h1 : (∑ w, beta * (A w * B w) * weight beta E A f w)
        = beta * ∑ w, (A w * B w) * weight beta E A f w := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring
    have h2 : (∑ w, beta * A w * weight beta E A f w)
        = beta * ∑ w, A w * weight beta E A f w := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring
    rw [h1, h2]
    simp only [expect]
    field_simp
  rw [← key]
  exact h

end Phys

