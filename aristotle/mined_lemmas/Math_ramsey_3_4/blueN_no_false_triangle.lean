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

lemma blueN_no_false_triangle (hsymm : ∀ x y, c x y = c y x)
    (hB : ∀ T : Finset (Fin 9), T.card = 4 → ¬ MonoClique c false T) (v : Fin 9)
    (T : Finset (Fin 9)) (hTsub : T ⊆ blueN c v) (hT3 : T.card = 3) :
    ¬ MonoClique c false T := by
  intro hm
  have hv : v ∉ T := by
    intro hvT
    have := hTsub hvT
    rw [mem_blueN] at this
    exact this.1 rfl
  refine hB (insert v T) ?_ (MonoClique.insert_vertex hsymm hm ?_)
  · rw [Finset.card_insert_of_notMem hv, hT3]
  · intro x hx
    have := hTsub hx
    rw [mem_blueN] at this
    exact this.2

