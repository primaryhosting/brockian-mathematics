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

/-
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
Basic definitions for the Kahn–Kalai theorem (Park–Pham proof):
the Bernoulli product measure on subsets of a finite ground set, covers,
`p`-smallness, up-sets, and the parameters `q(F)`, `p_c(F)`, `ℓ(F)`.
-/

namespace Math2

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Bernoulli(`p`) product weight of a subset `A` inside the ground set `g`. -/

lemma Emeas_split (ρ t : ℝ) (f : Finset α → ℝ) :
    Emeas (ρ + t - ρ * t) f = ∑ W : Finset α, w ρ W * Emeas t (fun V => f (W ∪ V)) := by
  have h := wg_union (α := α) ρ t Finset.univ f
  rw [Finset.powerset_univ] at h
  simp only [← w_eq_wg] at h
  rw [Emeas, ← h]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Emeas, Finset.mul_sum]

end Math2

/-
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Math2.Measure

/-!
Minimum fragments (Park–Pham) and the key counting lemma: the cover produced from the
edges with a large minimum fragment has small expected cost.
-/

namespace Math2

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The candidate fragments of `S` with respect to `W`: the sets `S' \ W` for edges
`S' ∈ H` contained in `W ∪ S`. -/
