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
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- A constraint graph: a finite multiset-free set of (directed) edges over `Fin numVerts`,
together with a Boolean binary constraint attached to every edge, over the alphabet
`Fin alphSize`. -/
structure ConstraintGraph where
  numVerts : ℕ
  alphSize : ℕ
  alph_pos : 0 < alphSize
  edges : Finset (Fin numVerts × Fin numVerts)
  edges_nonempty : edges.Nonempty
  sat : Fin numVerts × Fin numVerts → Fin alphSize → Fin alphSize → Bool

namespace ConstraintGraph

variable (G : ConstraintGraph)

/-- The number of edges (constraints) of `G`; the natural size measure. -/

theorem one_div_size_le_unsat (h : ¬ G.Satisfiable) : 1 / (G.size : ℝ) ≤ G.unsat := by
  have h1 : 1 ≤ G.minViolated := Nat.one_le_iff_ne_zero.2 fun hz =>
    h (G.minViolated_eq_zero_iff.1 hz)
  have hs : (0 : ℝ) < (G.size : ℝ) := by exact_mod_cast G.size_pos
  rw [unsat, div_le_div_iff_of_pos_right hs]
  exact_mod_cast h1

end ConstraintGraph

/-- A single-edge constraint graph whose only constraint is never satisfied; it witnesses that
the definitions above are not vacuous. -/
