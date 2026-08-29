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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib
import RequestProject.Savitch.Reach

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The deterministic simulator

This file defines the deterministic machine used in Savitch's theorem: an explicit
iterative (stack based) implementation of the recursive procedure

```
REACH d u v  =  if d = 0 then (u = v ∨ u → v)
                else ∃ m, REACH (d-1) u m ∧ REACH (d-1) m v
```

together with its encoding into bit strings and the space accounting: a well-formed
state occupies `O((f n)²)` bits, because the stack holds at most `f n + 2` frames of
`O(f n)` bits each.
-/

namespace CS
namespace Savitch

/-- Classical truth value of a proposition. -/

lemma mem_wordsOfLen : ∀ (k : ℕ) (w : Word), w ∈ wordsOfLen k ↔ w.length = k := by
  intro k
  induction k with
  | zero => intro w; cases w <;> simp [wordsOfLen]
  | succ k ih =>
    intro w
    cases w with
    | nil => simp [wordsOfLen]
    | cons b w =>
      simp only [wordsOfLen, List.mem_flatMap, List.length_cons, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨v, hv, hmem⟩
        simp only [List.mem_cons] at hmem
        rcases hmem with h | h | h
        · rw [(List.cons.injEq _ _ _ _ ▸ h : b = false ∧ w = v).2]; exact (ih v).1 hv
        · rw [(List.cons.injEq _ _ _ _ ▸ h : b = true ∧ w = v).2]; exact (ih v).1 hv
        · exact absurd h (by simp)
      · intro hw
        exact ⟨w, (ih w).2 hw, by cases b <;> simp⟩

