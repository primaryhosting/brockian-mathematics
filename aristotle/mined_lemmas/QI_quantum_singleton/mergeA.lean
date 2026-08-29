import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix
open scoped ComplexOrder

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

-- Note: the header block above is placed directly after `import Mathlib` because Lean requires
-- every `import` to precede all other commands, including module documentation comments.

namespace QI

/-! ## Auxiliary linear algebra: rank factorizations -/

/-- `LinearMap.toMatrix'` is inverse to `Matrix.mulVecLin`. -/

def mergeA {n q : ℕ} (SA SB : Finset (Fin n)) (b : {i : Fin n // i ∈ SB} → Fin q)
    (c : {i : Fin n // i ∈ (SA ∪ SB)ᶜ} → Fin q) : {i : Fin n // i ∉ SA} → Fin q := fun t =>
  if h : t.val ∈ SB then b ⟨t.val, h⟩
  else c ⟨t.val, Finset.mem_compl.mpr (by simp [Finset.mem_union, t.2, h])⟩

/-- Data off `SB`, assembled from data on `SA` and data on the rest. -/
