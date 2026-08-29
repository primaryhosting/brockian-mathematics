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

theorem erasureCorrectable_empty {n q K : ℕ} (ψ : Fin K → (Fin n → Fin q) → ℂ)
    (horth : ∀ i j : Fin K,
      (∑ x : Fin n → Fin q, ψ i x * (starRingEnd ℂ) (ψ j x)) = if i = j then 1 else 0) :
    ErasureCorrectable ψ ∅ := by
  refine ⟨fun _ _ => 1, fun i j a a' => ?_⟩
  rw [mul_one, ← horth i j]
  have hbij : Function.Bijective
      (fun y : {i : Fin n // i ∉ (∅ : Finset (Fin n))} → Fin q => glue ∅ a y) := by
    rw [Function.bijective_iff_has_inverse]
    refine ⟨fun x t => x t.val, fun y => ?_, fun x => ?_⟩
    · funext t
      simp [glue]
    · funext t
      simp [glue]
  refine Fintype.sum_bijective _ hbij _
    (fun x => ψ i x * (starRingEnd ℂ) (ψ j x)) (fun y => ?_)
  have hgl : glue (∅ : Finset (Fin n)) a' y = glue ∅ a y := by
    funext t
    simp [glue]
  rw [hgl]

/-- The trivial "code" consisting of the whole `n`-qudit space is an orthonormal family whose
empty-region erasures are correctable; hence the hypotheses of `quantum_singleton` are
satisfiable (here with `k = n` and `d = 1`). -/
