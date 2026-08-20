import Mathlib

/-!
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
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

namespace CS

/-- A *constraint graph* over the alphabet `Fin q`: a finite nonempty list (multiset) of
constraints, each of which is a pair of vertices together with a boolean predicate on the
pair of values assigned to them. -/
structure ConstraintGraph (q : ℕ) where
  /-- Number of vertices. -/
  numVerts : ℕ
  /-- The constraints (edges): a pair of endpoints and a boolean relation on their values. -/
  edges : List (Fin numVerts × Fin numVerts × (Fin q → Fin q → Bool))
  /-- Constraint graphs have at least one constraint. -/
  edges_ne : edges ≠ []

namespace ConstraintGraph

variable {q : ℕ} [NeZero q]

/-- The size of a constraint graph is its number of constraints. -/

lemma unsat_iterate_ge (halpha : 0 ≤ alpha)
    (hunsat : ∀ G, min (2 * G.unsat) alpha ≤ (step G).unsat) (t : ℕ) (G : ConstraintGraph q) :
    min (2 ^ t * G.unsat) alpha ≤ (step^[t] G).unsat := by
  induction t with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, one_mul]; exact min_le_left _ _
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      refine le_trans ?_ (hunsat (step^[t] G))
      have h2 : 2 * min (2 ^ t * G.unsat) alpha ≤ 2 * (step^[t] G).unsat := by linarith
      rcases le_total (2 ^ t * G.unsat) alpha with h | h
      · rw [min_eq_left h] at h2
        have : (2 : ℚ) ^ (t + 1) * G.unsat = 2 * (2 ^ t * G.unsat) := by ring
        rw [this]
        exact min_le_min h2 le_rfl
      · rw [min_eq_right h] at h2
        refine le_trans (min_le_right _ _) ?_
        exact le_min (by linarith) le_rfl

end Amplification

/-! ## Dinur's theorem

Starting from Dinur's *Main Lemma* (gap amplification: a size-linear transformation of
constraint graphs over a fixed alphabet which preserves satisfiability and doubles the `UNSAT`
value until it exceeds an absolute constant `alpha`), iterating it `⌈log₂ n⌉` times turns the
inverse-linear gap `1/n` of an unsatisfiable instance into the constant gap `alpha`, at a
polynomial cost in size.  This is the gap-amplification argument underlying the PCP theorem:
deciding whether a constraint graph is satisfiable or has `UNSAT` value at least `alpha` is as
hard as deciding satisfiability of constraint graphs, which is the "gap" (equivalently,
proof-checking) form of the PCP theorem. -/

/-- Auxiliary arithmetic fact: `2 ^ ⌈log₂ n⌉ ≤ 2 * n` for `n ≥ 1`. -/
