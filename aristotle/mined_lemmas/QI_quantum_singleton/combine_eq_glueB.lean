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

theorem combine_eq_glueB {n q : ℕ} (SA SB : Finset (Fin n)) (hdisj : Disjoint SA SB)
    (a : {i : Fin n // i ∈ SA} → Fin q) (b : {i : Fin n // i ∈ SB} → Fin q)
    (c : {i : Fin n // i ∈ (SA ∪ SB)ᶜ} → Fin q) :
    combine SA SB a b c = glue SB b (mergeB SA SB a c) := by
  funext t
  by_cases h : t ∈ SB
  · have hnA : t ∉ SA := Finset.disjoint_right.mp hdisj h
    simp [combine, glue, hnA, h]
  · by_cases h2 : t ∈ SA <;> simp [combine, glue, mergeB, h, h2]

