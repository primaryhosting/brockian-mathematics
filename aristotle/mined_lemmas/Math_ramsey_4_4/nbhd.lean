/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Math

open Finset SimpleGraph

/-- Extract four elements in increasing order from a four-element finset. -/

def nbhd (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (v : V) : Finset V :=
  (T.erase v).filter (fun w => G.Adj v w)

/-- The non-neighbours of `v` inside `T` (excluding `v`). -/
