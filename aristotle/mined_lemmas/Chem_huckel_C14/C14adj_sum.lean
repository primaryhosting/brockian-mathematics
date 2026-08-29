/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Chem

/-- The standard additive character `ZMod 14 → ℂ`, `j ↦ exp (2πI j / 14)`. -/

lemma C14adj_sum (i k : ZMod 14) :
    ∑ j : ZMod 14, C14adj i j * ee (j * k) = (ee k + ee (-k)) * ee (i * k) := by
  have hne : (i - 1 : ZMod 14) ≠ i + 1 := by
    intro h
    have : (2 : ZMod 14) = 0 := by linear_combination -h
    revert this; decide
  have hstep : ∀ j : ZMod 14, C14adj i j * ee (j * k)
      = if j ∈ ({i - 1, i + 1} : Finset (ZMod 14)) then ee (j * k) else 0 := by
    intro j
    have h1 : (i - j = 1) ↔ (j = i - 1) := by
      constructor <;> (intro h; linear_combination -h)
    have h2 : (i - j = -1) ↔ (j = i + 1) := by
      constructor <;> (intro h; linear_combination -h)
    simp only [C14adj, Matrix.circulant_apply, h1, h2, Finset.mem_insert,
      Finset.mem_singleton]
    split <;> simp
  rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_pair hne]
  have e1 : (i - 1) * k = i * k + -k := by ring
  have e2 : (i + 1) * k = i * k + k := by ring
  rw [e1, e2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  ring

