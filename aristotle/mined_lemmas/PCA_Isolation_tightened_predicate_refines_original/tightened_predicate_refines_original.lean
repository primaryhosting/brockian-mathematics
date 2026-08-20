import Mathlib

/-!
# Tightened Predicate Refines Original
Category: Proof-Carrying Apps
Target: PCA.Isolation.tightened_predicate_refines_original
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

namespace PCA.Isolation

variable {S A : Type*}

/-- The state reached from `s` by executing the finite action trace `l`
under the transition function `step`. -/

theorem tightened_predicate_refines_original (step : S → A → S) (P : S → Prop) :
    (∀ (n : ℕ) (s : S), tighten step P n s → P s) ∧
    (∀ (n : ℕ) (s : S), tighten step P (n + 1) s → tighten step P n s) ∧
    (∀ s : S, (∀ n : ℕ, tighten step P n s) ↔ ∀ l : List A, P (run step s l)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n s hs
    simpa using (tighten_iff_forall_traces step P n s).mp hs [] (by simp)
  · intro n s hs
    refine (tighten_iff_forall_traces step P n s).mpr fun l hl => ?_
    exact (tighten_iff_forall_traces step P (n + 1) s).mp hs l (hl.trans (Nat.le_succ n))
  · intro s
    constructor
    · intro h l
      exact (tighten_iff_forall_traces step P l.length s).mp (h l.length) l le_rfl
    · intro h n
      exact (tighten_iff_forall_traces step P n s).mpr fun l _ => h l

end PCA.Isolation

