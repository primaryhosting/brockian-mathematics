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
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open SimpleGraph Matrix Real

namespace Chem

/-- The adjacency matrix of the cycle graph `C₆`, over `ℂ`
(the Hückel matrix of benzene in units where `α = 0`, `β = 1`). -/

private lemma eigen_of (v : Fin 6 → ℂ) (c : ℂ) (hv : v 0 ≠ 0) (h : C6 *ᵥ v = c • v) :
    ∃ w : Fin 6 → ℂ, w ≠ 0 ∧ C6 *ᵥ w = c • w :=
  ⟨v, fun hc => hv (by simp [hc]), h⟩

/-- Each `2 cos (2πk/6)`, `k = 0,…,5`, is an eigenvalue of the adjacency matrix of `C₆`. -/
