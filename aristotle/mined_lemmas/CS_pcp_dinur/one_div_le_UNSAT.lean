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

/-!
## Constraint graphs (binary CSPs)

Dinur's proof of the PCP theorem is phrased in terms of *constraint graphs*: binary
constraint satisfaction problems whose variables are the vertices of a graph and whose
constraints sit on the edges.  We model such an instance by

* a number `n` of variables, indexed by `Fin n`;
* an alphabet `Fin q` with `q > 0`;
* a list `cs` of constraints, each a triple `(u, v, R)` with `u v : Fin n` and
  `R : Fin q → Fin q → Bool`.

An assignment is a map `Fin n → Fin q`, and the *unsat value* `UNSAT G` is the minimum,
over all assignments, of the fraction of constraints that are violated.
-/

/-- A binary constraint satisfaction instance ("constraint graph"): `n` variables taking
values in an alphabet of size `q > 0`, subject to a list of binary constraints. -/
structure ConstraintGraph where
  /-- Number of variables. -/
  n : ℕ
  /-- Size of the alphabet. -/
  q : ℕ
  /-- The alphabet is nonempty. -/
  hq : 0 < q
  /-- The list of constraints, each relating two variables. -/
  cs : List (Fin n × Fin n × (Fin q → Fin q → Bool))

namespace ConstraintGraph

variable (G : ConstraintGraph)

/-- The "all-zero" assignment; it exists because the alphabet is nonempty. -/

lemma one_div_le_UNSAT (h : 0 < G.UNSAT) : 1 / (G.cs.length : ℚ) ≤ G.UNSAT := by
  obtain ⟨a, ha⟩ := (exists_unsatFrac_eq_UNSAT (G := G))
  have hm : 0 < G.cs.length := cs_length_pos_of_UNSAT_pos h
  have hmQ : (0 : ℚ) < (G.cs.length : ℚ) := by exact_mod_cast hm
  have hpos : 0 < (G.unsatCount a : ℚ) / (G.cs.length : ℚ) := by
    rw [← unsatFrac, ← ha]; exact h
  have hc1 : 1 ≤ (G.unsatCount a : ℚ) := by
    by_contra hcon
    push_neg at hcon
    have : G.unsatCount a = 0 := by
      have : (G.unsatCount a : ℚ) < 1 := hcon
      exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
    simp [this] at hpos
  rw [ha, unsatFrac]
  exact (div_le_div_iff_of_pos_right hmQ).mpr hc1

end ConstraintGraph

open ConstraintGraph

/-!
## Dinur's gap amplification, iterated

Dinur's *Main Lemma* provides, for a fixed alphabet size `q₀`, a transformation `amp` of
constraint graphs with:

* linear size blow-up: `size (amp G) ≤ C * size G`;
* perfect completeness: `amp G` is satisfiable whenever `G` is;
* gap amplification: `UNSAT (amp G) ≥ min (2 * UNSAT G) α` for a fixed constant `α > 0`.

The PCP theorem follows by iterating `amp` a logarithmic number of times.  The lemmas
below carry out this iteration, and `CS.pcp_dinur` records the resulting statement.
-/

section Amplification

variable (amp : ConstraintGraph → ConstraintGraph) (C : ℕ) (α : ℚ)

/-- Iterating the size bound. -/
