import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
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

namespace Chem

open scoped Matrix

/-! ### A primitive 14-th root of unity and the associated character -/

/-- A primitive 14-th root of unity. -/

theorem adj_eq_conj :
    (SimpleGraph.cycleGraph 14).adjMatrix ℂ = Fm * Dm * Gm := by
  calc (SimpleGraph.cycleGraph 14).adjMatrix ℂ
      = (SimpleGraph.cycleGraph 14).adjMatrix ℂ * (Fm * Gm) := by rw [Fm_mul_Gm, Matrix.mul_one]
    _ = ((SimpleGraph.cycleGraph 14).adjMatrix ℂ * Fm) * Gm := by rw [Matrix.mul_assoc]
    _ = Fm * Dm * Gm := by rw [adj_mul_Fm]

/-- **Hückel theory for `C₁₄`**: the eigenvalues (the spectrum) of the adjacency matrix of the
cycle graph `C₁₄` are exactly the numbers `2 cos (2πk/14)`, `k = 0, …, 13`. -/
