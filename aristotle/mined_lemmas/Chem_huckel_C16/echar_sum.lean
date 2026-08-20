/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not allow a module docstring before the import commands, so the required
header appears here as an ordinary block comment; the text is otherwise verbatim.)
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

open Complex Polynomial Matrix SimpleGraph

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₁₆`, i.e. the Hückel matrix of
cyclic C₁₆ in units where the Coulomb integral is `0` and the resonance integral is `1`. -/

theorem echar_sum (b : Fin 16) :
    (∑ k : Fin 16, echar (k * b)) = if b = 0 then (16 : ℂ) else 0 := by
  simp only [echar_mul_pow]
  by_cases hb : b = 0
  · subst hb
    simp [echar]
  · rw [if_neg hb]
    have hw : echar b ≠ 1 := fun h => hb ((echar_eq_one_iff b).1 h)
    rw [Fin.sum_univ_eq_sum_range (fun k => (echar b) ^ k) 16, geom_sum_eq hw,
      echar_pow_sixteen]
    simp

