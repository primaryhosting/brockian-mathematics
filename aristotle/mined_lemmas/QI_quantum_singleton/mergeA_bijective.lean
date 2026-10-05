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

theorem mergeA_bijective {n q : ℕ} (SA SB : Finset (Fin n)) (hdisj : Disjoint SA SB) :
    Function.Bijective (fun bc : ({i : Fin n // i ∈ SB} → Fin q) ×
      ({i : Fin n // i ∈ (SA ∪ SB)ᶜ} → Fin q) => mergeA SA SB bc.1 bc.2) := by
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun y => (fun s => y ⟨s.val, Finset.disjoint_right.mp hdisj s.2⟩,
    fun s => y ⟨s.val, notMem_left_of_mem_compl_union s.2⟩), ?_, ?_⟩
  · rintro ⟨b, c⟩
    refine Prod.ext ?_ ?_ <;> funext s
    · simp [mergeA, s.2]
    · have hs := s.2
      simp only [Finset.mem_compl, Finset.mem_union, not_or] at hs
      simp [mergeA, hs.2]
  · intro y
    funext t
    by_cases h : t.val ∈ SB <;> simp [mergeA, h]

