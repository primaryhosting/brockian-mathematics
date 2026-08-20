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

lemma two_pow_clog_le (n : ℕ) (hn : 1 ≤ n) : 2 ^ Nat.clog 2 n ≤ 2 * n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · simp
  · have hc : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) h
    have hlt : 2 ^ (Nat.clog 2 n - 1) < n := Nat.pow_pred_clog_lt_self (by norm_num) h
    have : 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [this]
    omega

/-- **Dinur's gap amplification theorem (PCP theorem, gap form).**

Assume Dinur's Main Lemma for constraint graphs over the fixed alphabet `Fin q`: there are
constants `C` and `alpha ∈ (0, 1]` and a transformation `step` of constraint graphs which
* preserves satisfiability,
* increases the size by at most a factor `C`,
* and doubles the `UNSAT` value, up to the ceiling `alpha`.

Then there is a *gap-producing* reduction `R`, of polynomial size blow-up, that maps satisfiable
constraint graphs to satisfiable constraint graphs, and unsatisfiable ones to constraint graphs
whose `UNSAT` value is at least the absolute constant `alpha`. -/
