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

theorem prob_inter_eq_sum_cells (p : Ω → ℝ) (E : Finset Ω) (hI : IsInfoPartition I)
    (hM : ∀ ω ∈ M, I ω ⊆ M) :
    ∑ C ∈ M.image I, prob p (E ∩ C) = prob p (E ∩ M) := by
  have key : ∀ S : Finset Ω, prob p (E ∩ S) = ∑ ω ∈ S, (if ω ∈ E then p ω else 0) := by
    intro S
    rw [Finset.inter_comm, prob, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
  simp only [key]
  exact sum_over_cells hI hM _

/-- **Key computation.** If, throughout a union `M` of cells, an agent's conditional
probability of `E` given their cell equals `q`, then the unconditional probability of `E`
given `M` also equals `q` (in the product form `prob p (E ∩ M) = q * prob p M`). -/
