/-
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## Complex conjugation on a complexified rational vector space -/

/-- Complex conjugation, viewed as a `ℚ`-linear endomorphism of `ℂ`. -/

noncomputable def tateHodgeStructure (V : Type) [AddCommGroup V] [Module ℚ V] (p : ℤ) :
    HodgeStructure (2 * p) V where
  piece k := if k = p then ⊤ else ⊥
  internal := isInternal_single p
  conj_piece k := by
    by_cases h : k = p
    · subst h
      have hk : 2 * k - k = k := by ring
      simp [hk, Submodule.map_top, LinearMap.range_eq_top.2 (conjTensor_surjective V)]
    · have h2 : 2 * p - k ≠ p := by omega
      simp [h, h2]

