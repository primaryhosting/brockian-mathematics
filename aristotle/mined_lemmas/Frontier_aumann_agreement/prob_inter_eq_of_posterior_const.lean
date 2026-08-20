import Mathlib

/-!
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

variable {Ω : Type*} [DecidableEq Ω]

/-- The prior probability of a (finite) event `S`, computed from the point masses `p`. -/

theorem prob_inter_eq_of_posterior_const {p : Ω → ℝ} {E : Finset Ω} {q : ℝ}
    (hI : IsInfoPartition I) (hM : ∀ ω ∈ M, I ω ⊆ M)
    (hpost : ∀ ω ∈ M, 0 < prob p (I ω) ∧ prob p (E ∩ I ω) / prob p (I ω) = q) :
    prob p (E ∩ M) = q * prob p M := by
  rw [← prob_inter_eq_sum_cells p E hI hM, ← prob_eq_sum_cells p hI hM, Finset.mul_sum]
  refine Finset.sum_congr rfl fun C hC => ?_
  obtain ⟨ω₀, hω₀M, hω₀⟩ := Finset.mem_image.mp hC
  obtain ⟨hpos, heq⟩ := hpost ω₀ hω₀M
  rw [hω₀] at hpos heq
  field_simp at heq
  linarith [heq]

end Partition

/-- **Aumann's agreement theorem** (finite common-prior version): two agents with a common
prior `p` and information partitions `I₁`, `I₂` cannot agree to disagree.  If it is common
knowledge (on the event `M`, which contains the actual state `ω₀`) that agent 1 assigns
posterior probability `q₁` to the event `E` and agent 2 assigns posterior probability `q₂`,
then `q₁ = q₂`.

The hypothesis `hp1` (that the prior is normalised) is included because a common prior is a
probability distribution; the argument itself only uses non-negativity together with the fact
that the cells occurring in `M` have positive prior mass. -/
