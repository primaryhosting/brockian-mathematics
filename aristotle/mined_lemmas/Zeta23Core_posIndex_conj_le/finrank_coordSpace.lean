import Mathlib

/-!
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m]
  [Fintype d] [DecidableEq d]

/-- The real quadratic form associated with a matrix `Q`: `x ↦ Re (xᴴ Q x)`. -/

lemma finrank_coordSpace (s : Finset m) :
    Module.finrank 𝕜 (coordSpace (𝕜 := 𝕜) s) = s.card := by
  have hli : LinearIndependent 𝕜 (fun i : s => (Pi.single (i : m) (1 : 𝕜) : m → 𝕜)) := by
    have h := (Pi.basisFun 𝕜 m).linearIndependent
    have h2 := h.comp (fun i : s => (i : m)) Subtype.val_injective
    simpa [Function.comp_def] using h2
  rw [coordSpace, finrank_span_eq_card hli]
  simp

omit [Fintype m] in
