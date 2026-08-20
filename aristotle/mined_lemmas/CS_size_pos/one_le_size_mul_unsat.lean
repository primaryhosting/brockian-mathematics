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

lemma one_le_size_mul_unsat (G : ConstraintGraph q) (h : ¬ G.Satisfiable) :
    1 ≤ (G.size : ℚ) * G.unsat := by
  obtain ⟨a, ha⟩ := G.exists_unsat_eq
  have h1 : 1 ≤ G.unsatCount a := by
    rcases Nat.eq_zero_or_pos (G.unsatCount a) with h0 | h0
    · exact absurd ⟨a, (G.unsatCount_eq_zero_iff a).mp h0⟩ h
    · exact h0
  have hs : (0 : ℚ) < (G.size : ℚ) := by exact_mod_cast G.size_pos
  rw [ha]
  unfold unsatFrac
  rw [mul_div_cancel₀ _ hs.ne']
  exact_mod_cast h1

end ConstraintGraph

open ConstraintGraph

/-! ## Iterating the amplification step -/

section Amplification

variable {q : ℕ} [NeZero q]
variable (C : ℕ) (alpha : ℚ) (step : ConstraintGraph q → ConstraintGraph q)

omit [NeZero q] in
/-- Iterating the amplification step preserves satisfiability. -/
