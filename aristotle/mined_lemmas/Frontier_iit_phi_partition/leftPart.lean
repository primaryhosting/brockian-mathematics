/-
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
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

namespace Frontier

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The restriction of a global state `x` to the part `A` of the system. -/

def leftPart : Finset (Fin 2) := {0}

instance : Unique (↥leftPart) where
  default := ⟨0, by decide⟩
  uniq i := Subtype.ext (Finset.mem_singleton.mp i.2)

instance : Unique (↥leftPartᶜ) where
  default := ⟨1, by decide⟩
  uniq i := by
    have h : (i : Fin 2) ∉ leftPart := Finset.mem_compl.mp i.2
    have h' : (i : Fin 2) ≠ 0 := fun hc => h (by simp [leftPart, hc])
    have h2 : ∀ j : Fin 2, j ≠ 0 → j = 1 := by decide
    exact Subtype.ext (h2 _ h')

