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

lemma redN_mono_false (hsymm : ∀ x y, c x y = c y x)
    (hR : ∀ T : Finset (Fin 9), T.card = 3 → ¬ MonoClique c true T) (v : Fin 9) :
    MonoClique c false (redN c v) := by
  intro x hx y hy hxy
  rw [mem_redN] at hx hy
  by_contra hc
  have hxytrue : c x y = true := by simpa using hc
  refine hR {v, x, y} ?_ ?_
  · rw [Finset.card_eq_three]
    exact ⟨v, x, y, (Ne.symm hx.1), (Ne.symm hy.1), hxy, rfl⟩
  · have hT : MonoClique c true {x, y} := by
      intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact hxytrue
      · rw [hsymm]; exact hxytrue
      · exact absurd rfl hab
    refine MonoClique.insert_vertex hsymm hT ?_
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hx.2
    · exact hy.2

/-- With no `false` `K₄`, the `false`-neighbourhood of a vertex has no `false` triangle. -/
