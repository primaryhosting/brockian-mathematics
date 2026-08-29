/-
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
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

set_option grind.warning false

namespace Phys

/-! ### The 18 vectors

We use the Cabello–Estebaranz–García-Alcaine 18-vector, 9-basis Kochen–Specker set in `ℝ⁴`.
The vectors have integer coordinates, listed here as rows. -/

/-- Integer coordinates of the 18 Kochen–Specker vectors. -/

lemma ctx_sum_eq_one {f : Fin 18 → Bool} (hf : IsKSColoring f) (a b c d : Fin 18)
    (h : ksDot a b = 0 ∧ ksDot a c = 0 ∧ ksDot a d = 0 ∧ ksDot b c = 0 ∧ ksDot b d = 0 ∧
      ksDot c d = 0) :
    colVal f a + colVal f b + colVal f c + colVal f d = 1 := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := h
  obtain ⟨hexcl, hbasis⟩ := hf
  have hone := hbasis a b c d (ksVec_orthogonal hab) (ksVec_orthogonal hac)
    (ksVec_orthogonal had) (ksVec_orthogonal hbc) (ksVec_orthogonal hbd) (ksVec_orthogonal hcd)
  have eab := hexcl a b (ksVec_orthogonal hab)
  have eac := hexcl a c (ksVec_orthogonal hac)
  have ead := hexcl a d (ksVec_orthogonal had)
  have ebc := hexcl b c (ksVec_orthogonal hbc)
  have ebd := hexcl b d (ksVec_orthogonal hbd)
  have ecd := hexcl c d (ksVec_orthogonal hcd)
  unfold colVal
  cases ha : f a <;> cases hb : f b <;> cases hc : f c <;> cases hd : f d <;> simp_all

/-- **Kochen–Specker theorem (18-vector version).**  The explicit 18-vector configuration in
`ℝ⁴` admits no `{0,1}`-coloring. -/
