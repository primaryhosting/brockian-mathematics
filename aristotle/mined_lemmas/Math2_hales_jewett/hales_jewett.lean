import Mathlib

/-!
# Hales Jewett
Category: Frontier Math
Target: Math2.hales_jewett
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

namespace Math2

/-- `IsCombLine N k L` says that `L : Fin k → (Fin N → Fin k)` is a *combinatorial line* in the
hypercube `Fin N → Fin k`: there is a word `f : Fin N → Option (Fin k)` such that in coordinate
`i` the point `L x` is the constant `a` when `f i = some a`, and is the "moving" letter `x` when
`f i = none`, and at least one coordinate is moving. -/

theorem hales_jewett (r k : ℕ) :
    ∃ N : ℕ, ∀ C : (Fin N → Fin k) → Fin r,
      ∃ L : Fin k → Fin N → Fin k,
        IsCombLine N k L ∧ ∃ c : Fin r, ∀ x : Fin k, C (L x) = c := by
  obtain ⟨ι, ιfin, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin k) (Fin r)
  classical
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  refine ⟨Fintype.card ι, fun C ↦ ?_⟩
  obtain ⟨l, c, cl⟩ := hι fun v ↦ C (v ∘ e.symm)
  refine ⟨fun x i ↦ (l.idxFun (e.symm i)).getD x,
    ⟨fun i ↦ l.idxFun (e.symm i), ?_, fun x i ↦ rfl⟩, c, fun x ↦ ?_⟩
  · obtain ⟨i, hi⟩ := l.proper
    exact ⟨e i, by simpa using hi⟩
  · simpa [Function.comp_def, Combinatorics.Line.apply_def] using cl x

end Math2

