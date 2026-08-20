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

set_option grind.warning false

namespace Chem

open Polynomial Complex

instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- The cycle graph `C₁₃`, on the vertex set `ZMod 13`, where `i` and `j` are adjacent
iff they differ by `1`. -/

def C13 : SimpleGraph (ZMod 13) := SimpleGraph.fromRel (fun i j => j = i + 1)

instance : DecidableRel C13.Adj := fun i j => by
  unfold C13 SimpleGraph.fromRel; infer_instance

/-- The adjacency matrix of the cycle graph `C₁₃`, with complex entries. -/
