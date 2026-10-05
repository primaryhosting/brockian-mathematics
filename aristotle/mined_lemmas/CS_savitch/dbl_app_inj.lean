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

lemma dbl_app_inj : ∀ (w₁ w₂ r₁ r₂ : Word), dbl w₁ ++ r₁ = dbl w₂ ++ r₂ → w₁ = w₂ ∧ r₁ = r₂ := by
  intro w₁
  induction w₁ with
  | nil =>
    intro w₂ r₁ r₂ h
    cases w₂ with
    | nil => simpa using h
    | cons b w =>
      exfalso
      rw [dbl_nil, dbl_cons] at h
      cases b <;> simp at h
  | cons b₁ w₁ ih =>
    intro w₂ r₁ r₂ h
    cases w₂ with
    | nil =>
      exfalso
      rw [dbl_nil, dbl_cons] at h
      cases b₁ <;> simp at h
    | cons b₂ w₂ =>
      rw [dbl_cons, dbl_cons] at h
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨hb, -, h⟩ := h
      obtain ⟨hw, hr⟩ := ih w₂ r₁ r₂ h
      exact ⟨by rw [hb, hw], hr⟩

/-- Encoding of a list of "registers" (words) into a single word. -/
