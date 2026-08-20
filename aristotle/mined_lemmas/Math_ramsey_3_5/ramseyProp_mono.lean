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

/-
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-! ## Relative (Finset-localized) triangles and independent sets -/

section Rel

variable {V : Type*} [LinearOrder V]

/-- `t` is an independent set of `G`. -/

lemma ramseyProp_mono {n m : ℕ} (hnm : n ≤ m) (h : RamseyProp n) : RamseyProp m := by
  classical
  intro G
  set f : Fin n → Fin m := fun i => ⟨i.1, lt_of_lt_of_le i.2 hnm⟩ with hf
  have hfinj : Function.Injective f := by
    intro a b hab
    simpa [hf, Fin.ext_iff] using hab
  rcases h (SimpleGraph.comap f G) with ⟨s, hc, hadj⟩ | ⟨s, hc, hind⟩
  · refine Or.inl ⟨s.image f, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hfinj, hc]
    · intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      exact hadj a ha b hb (fun h => hxy (by rw [h]))
  · refine Or.inr ⟨s.image f, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hfinj, hc]
    · intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      exact hind a ha b hb (fun h => hxy (by rw [h]))

/-! ## The lower bound: the circulant graph `C₁₃(1,5)` -/

/-- Adjacency of the circulant graph on `ℤ/13` with connection set `{±1, ±5}`. -/
