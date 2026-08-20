/-
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header
-- above is repeated below as the module docstring.)

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

/-- A *constraint graph* over the alphabet `Fin q`: a finite (multi)graph on the vertex
set `Fin numV` with `numE` edges, each edge carrying a binary constraint on the values
assigned to its endpoints.  This is the combinatorial object manipulated throughout
Dinur's proof of the PCP theorem. -/
structure ConstraintGraph (q : ℕ) where
  /-- number of vertices -/
  numV : ℕ
  /-- number of edges -/
  numE : ℕ
  /-- the endpoints of each edge -/
  edge : Fin numE → Fin numV × Fin numV
  /-- the constraint attached to each edge -/
  sat : Fin numE → (Fin q → Fin q → Bool)
  /-- constraint graphs have at least one edge -/
  edge_pos : 0 < numE

variable {q : ℕ} [NeZero q]

/-- The set of edges violated by an assignment `σ`. -/

lemma iterate_size (hC : 1 ≤ C)
    (hsize : ∀ G : ConstraintGraph q, ((A G).numE : ℚ) ≤ C * (G.numE : ℚ))
    (k : ℕ) (G : ConstraintGraph q) :
    ((A^[k] G).numE : ℚ) ≤ C ^ k * (G.numE : ℚ) := by
  induction k generalizing G with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      have h1 : ((A^[k] (A G)).numE : ℚ) ≤ C ^ k * ((A G).numE : ℚ) := ih (A G)
      have h2 : ((A G).numE : ℚ) ≤ C * (G.numE : ℚ) := hsize G
      have hk : (0 : ℚ) ≤ C ^ k := by positivity
      calc ((A^[k] (A G)).numE : ℚ) ≤ C ^ k * ((A G).numE : ℚ) := h1
        _ ≤ C ^ k * (C * (G.numE : ℚ)) := by nlinarith
        _ = C ^ (k + 1) * (G.numE : ℚ) := by ring

end Amplification

/-- Auxiliary bound: `2 ^ (Nat.clog 2 m) ≤ 2 * m` for `m ≥ 1`. -/
