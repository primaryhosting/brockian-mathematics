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

lemma not_ramseyProp_13 : ¬ RamseyProp 13 := by
  intro h
  rcases h C13 with ⟨s, hc, hadj⟩ | ⟨s, hc, hind⟩
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hc
    exact C13_triangle_free a b c
      (hadj a (by simp) b (by simp) hab)
      (hadj b (by simp) c (by simp) hbc)
      (hadj a (by simp) c (by simp) hac)
  · set g := s.orderIsoOfFin hc with hg
    set f : Fin 5 → Fin 13 := fun i => (g i : Fin 13) with hfdef
    have hmem : ∀ i, f i ∈ s := fun i => (g i).2
    have hlt : ∀ i j : Fin 5, i < j → f i < f j := fun i j hij => g.lt_iff_lt.mpr hij
    have key := C13_no_indep5 (f 0) (f 1) (f 2) (f 3) (f 4)
      (hlt 0 1 (by decide)) (hlt 1 2 (by decide)) (hlt 2 3 (by decide)) (hlt 3 4 (by decide))
    have hnadj : ∀ i j : Fin 5, i < j → cB (f i) (f j) = false := by
      intro i j hij
      have hne : f i ≠ f j := ne_of_lt (hlt i j hij)
      have := hind (f i) (hmem i) (f j) (hmem j) hne
      simpa [C13] using this
    rcases key with h | h | h | h | h | h | h | h | h | h
    · simp [hnadj 0 1 (by decide)] at h
    · simp [hnadj 0 2 (by decide)] at h
    · simp [hnadj 0 3 (by decide)] at h
    · simp [hnadj 0 4 (by decide)] at h
    · simp [hnadj 1 2 (by decide)] at h
    · simp [hnadj 1 3 (by decide)] at h
    · simp [hnadj 1 4 (by decide)] at h
    · simp [hnadj 2 3 (by decide)] at h
    · simp [hnadj 2 4 (by decide)] at h
    · simp [hnadj 3 4 (by decide)] at h

/-- **R(3,5) = 14**: 14 is the least `n` such that every graph on `n` vertices contains a
triangle or an independent set of size 5. -/
