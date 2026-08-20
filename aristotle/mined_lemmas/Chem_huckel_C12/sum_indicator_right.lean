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
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/

lemma sum_indicator_right (l : ZMod 12) (u : ZMod 12 → ℂ) :
    ∑ j : ZMod 12, u j * (if l = j + 1 ∨ l = j - 1 then (1 : ℂ) else 0)
      = u (l - 1) + u (l + 1) := by
  have h1 : ∀ j : ZMod 12, u j * (if l = j + 1 ∨ l = j - 1 then (1 : ℂ) else 0)
      = if j = l - 1 ∨ j = l + 1 then u j else 0 := by
    intro j
    rw [if_congr (cond_iff j l) rfl rfl]
    split <;> simp
  rw [Finset.sum_congr rfl (fun j _ => h1 j), ← Finset.sum_filter]
  have h2 : Finset.univ.filter (fun j : ZMod 12 => j = l - 1 ∨ j = l + 1) = {l - 1, l + 1} := by
    ext j; simp
  have h3 : (l : ZMod 12) - 1 ≠ l + 1 := fun h => (ne_add_one_sub_one l) h.symm
  rw [h2, Finset.sum_pair h3]

/-- The Fourier matrices are inverse to each other up to the factor 12. -/
