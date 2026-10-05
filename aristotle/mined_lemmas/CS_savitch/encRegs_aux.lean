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

lemma encRegs_aux : ∀ (l₁ l₂ : List Word) (r₁ r₂ : Word),
    (l₁.flatMap dbl) ++ ([false, true] ++ r₁) = (l₂.flatMap dbl) ++ ([false, true] ++ r₂) →
    l₁ = l₂ ∧ r₁ = r₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ r₁ r₂ h
    cases l₂ with
    | nil => simpa using h
    | cons w l =>
      exfalso
      simp only [List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_assoc] at h
      cases w with
      | nil => rw [dbl_nil] at h; simp at h
      | cons b w =>
        rw [dbl_cons] at h
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨h1, h2, -⟩ := h
        simp [← h1] at h2
  | cons w₁ l₁ ih =>
    intro l₂ r₁ r₂ h
    cases l₂ with
    | nil =>
      exfalso
      simp only [List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_assoc] at h
      cases w₁ with
      | nil => rw [dbl_nil] at h; simp at h
      | cons b w =>
        rw [dbl_cons] at h
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨h1, h2, -⟩ := h
        simp [h1] at h2
    | cons w₂ l₂ =>
      simp only [List.flatMap_cons, List.append_assoc] at h
      obtain ⟨hw, h⟩ := dbl_app_inj _ _ _ _ h
      obtain ⟨hl, hr⟩ := ih l₂ r₁ r₂ h
      exact ⟨by rw [hw, hl], hr⟩

