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

theorem tighten_iff_forall_traces (step : S → A → S) (P : S → Prop) :
    ∀ (n : ℕ) (s : S),
      tighten step P n s ↔ ∀ l : List A, l.length ≤ n → P (run step s l) := by
  intro n
  induction n with
  | zero =>
      intro s
      constructor
      · intro hs l hl
        have : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
        subst this
        simpa using hs
      · intro h
        simpa using h [] (by simp)
  | succ n ih =>
      intro s
      constructor
      · rintro ⟨hP, hstep⟩ l hl
        cases l with
        | nil => simpa using hP
        | cons a t =>
            have ht : t.length ≤ n := by
              simpa [List.length_cons, Nat.succ_le_succ_iff] using hl
            have := (ih (step s a)).mp (hstep a) t ht
            simpa using this
      · intro h
        refine ⟨by simpa using h [] (by simp), fun a => ?_⟩
        refine (ih (step s a)).mpr fun t ht => ?_
        have := h (a :: t) (by simpa [List.length_cons] using Nat.succ_le_succ ht)
        simpa using this

/-- **Soundness, monotonicity and completeness of the isolation engine's model.**

1. *Refinement*: every tightened predicate implies the original predicate `P`.
2. *Monotone tightening*: each further round of tightening only shrinks the
   admitted set of states.
3. *Completeness of the limit*: a state satisfies every round of tightening
   precisely when no finite trace of actions can ever leave `P`. -/
