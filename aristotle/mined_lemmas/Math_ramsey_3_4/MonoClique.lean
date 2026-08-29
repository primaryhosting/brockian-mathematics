import Mathlib
/-!
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
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

namespace Math

/-- `MonoClique c b T` says that all pairs of distinct vertices of `T` get colour `b`
under the (edge-)colouring `c`. -/

lemma MonoClique.insert_vertex {n : ℕ} {c : Fin n → Fin n → Bool} {b : Bool}
    {T : Finset (Fin n)} {v : Fin n} (hsymm : ∀ x y, c x y = c y x)
    (hT : MonoClique c b T) (hv : ∀ x ∈ T, c v x = b) :
    MonoClique c b (insert v T) := by
  intro x hx y hy hxy
  simp only [Finset.mem_insert] at hx hy
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · exact absurd rfl hxy
    · exact hv y hy
  · rcases hy with rfl | hy
    · rw [hsymm]; exact hv x hx
    · exact hT x hx y hy hxy

section Nine

variable {c : Fin 9 → Fin 9 → Bool}

/-- The `true`-neighbourhood of a vertex. -/
