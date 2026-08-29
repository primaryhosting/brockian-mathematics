import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma qq_mem {L p : ℝ} (hδ0 : 0 ≤ L * p) (hδ1 : L * p ≤ 1) :
    ∀ ℓ : ℕ, 0 ≤ qq L p ℓ ∧ qq L p ℓ ≤ 1 := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    match ℓ with
    | 0 => simp [qq_zero]
    | (n + 1) =>
      obtain ⟨h1, h2⟩ := ih ((n + 1) / 2) (by omega)
      rw [qq_succ]
      constructor <;> nlinarith

end Math2

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

import RequestProject.Frag

/-!
# The Park–Pham key lemma

The cover built from the minimum fragments of one random round has small expected cost.
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

