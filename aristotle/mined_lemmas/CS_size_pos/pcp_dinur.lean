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

theorem pcp_dinur {q : ℕ} [NeZero q]
    (C : ℕ) (alpha : ℚ) (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (step : ConstraintGraph q → ConstraintGraph q)
    (hsat : ∀ G, G.Satisfiable → (step G).Satisfiable)
    (hsize : ∀ G, (step G).size ≤ C * G.size)
    (hunsat : ∀ G, min (2 * G.unsat) alpha ≤ (step G).unsat) :
    ∃ (R : ConstraintGraph q → ConstraintGraph q) (d : ℕ),
      (∀ G, G.Satisfiable → (R G).Satisfiable) ∧
      (∀ G, ¬ G.Satisfiable → alpha ≤ (R G).unsat) ∧
      (∀ G, (R G).size ≤ (2 * G.size) ^ d * G.size) := by
  classical
  refine ⟨fun G => step^[Nat.clog 2 G.size] G, Nat.clog 2 C, ?_, ?_, ?_⟩
  · intro G hG
    exact satisfiable_iterate step hsat _ G hG
  · intro G hG
    have key := unsat_iterate_ge alpha step halpha0.le hunsat (Nat.clog 2 G.size) G
    refine le_trans ?_ key
    refine le_min ?_ le_rfl
    -- `2 ^ ⌈log₂ n⌉ * UNSAT(G) ≥ n * (1/n) = 1 ≥ alpha`
    have hbase : 1 ≤ (G.size : ℚ) * G.unsat := G.one_le_size_mul_unsat hG
    have hle : (G.size : ℚ) ≤ (2 : ℚ) ^ Nat.clog 2 G.size := by
      have : G.size ≤ 2 ^ Nat.clog 2 G.size := Nat.le_pow_clog (by norm_num) _
      exact_mod_cast this
    have hu : 0 ≤ G.unsat := G.unsat_nonneg
    nlinarith [mul_le_mul_of_nonneg_right hle hu]
  · intro G
    have h1 : (step^[Nat.clog 2 G.size] G).size ≤ C ^ Nat.clog 2 G.size * G.size :=
      size_iterate_le C step hsize _ G
    have h2 : C ^ Nat.clog 2 G.size ≤ (2 * G.size) ^ Nat.clog 2 C := by
      calc C ^ Nat.clog 2 G.size ≤ (2 ^ Nat.clog 2 C) ^ Nat.clog 2 G.size :=
            Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) _) _
        _ = (2 ^ Nat.clog 2 G.size) ^ Nat.clog 2 C := by
            rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ ≤ (2 * G.size) ^ Nat.clog 2 C :=
            Nat.pow_le_pow_left (two_pow_clog_le G.size G.size_pos) _
    exact le_trans h1 (Nat.mul_le_mul_right _ h2)

/-! ## Non-degeneracy

Two concrete constraint graphs, witnessing that satisfiability of constraint graphs is a
nontrivial notion (both satisfiable and unsatisfiable instances exist) and that the base gap
