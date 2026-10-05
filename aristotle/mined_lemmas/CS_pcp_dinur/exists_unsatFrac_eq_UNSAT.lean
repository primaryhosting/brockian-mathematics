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

lemma exists_unsatFrac_eq_UNSAT : ∃ a : Fin G.n → Fin G.q, G.UNSAT = G.unsatFrac a := by
  have h := Finset.min'_mem _ G.image_unsatFrac_nonempty
  rw [Finset.mem_image] at h
  obtain ⟨a, -, ha⟩ := h
  exact ⟨a, ha.symm⟩

