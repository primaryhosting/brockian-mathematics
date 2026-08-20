import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
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

namespace QI

open Complex Finset

/-! ## The two-qubit vectors used in the PBR argument -/

/-- The normalisation constant `1/√2`. -/

noncomputable def quantumModel : OnticModel (Fin 2) where
  mu a l := if a = l then 1 else 0
  mu_nonneg := by intro a l; split <;> norm_num
  mu_sum := by intro a; simp
  resp i p := bornProb i p.1 p.2
  resp_nonneg := by intro i p; exact Complex.normSq_nonneg _
  resp_sum := by intro p; exact born_sum p.1 p.2
  born := by
    intro i a b
    fin_cases a <;> fin_cases b <;>
      simp [Fintype.sum_prod_type]

variable {Λ : Type} [Fintype Λ]

