/-
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxRecDepth 10000

namespace Math


def pentagonGraph : SimpleGraph (Fin 5) where
  Adj i j := (i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val
  symm := by intro i j h; tauto
  loopless := ⟨by intro i; simp; omega⟩

instance : DecidableRel pentagonGraph.Adj := fun i j => by
  unfold pentagonGraph; infer_instance

/-- The 5-cycle has no triangle, and neither does its complement. -/
