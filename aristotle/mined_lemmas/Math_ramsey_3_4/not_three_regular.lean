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

lemma not_three_regular (hsymm : ∀ x y, c x y = c y x)
    (hdeg : ∀ v, (redN c v).card = 3) : False := by
  classical
  let G : SimpleGraph (Fin 9) :=
  { Adj := fun u v => u ≠ v ∧ c u v = true
    symm := by
      rintro u v ⟨h1, h2⟩
      exact ⟨h1.symm, by rw [hsymm]; exact h2⟩
    loopless := by
      constructor
      rintro u ⟨h1, -⟩
      exact h1 rfl }
  have hdG : ∀ v, G.degree v = 3 := by
    intro v
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, ← hdeg v]
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_redN, G]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2⟩
  have h := SimpleGraph.sum_degrees_eq_twice_card_edges G
  simp only [hdG, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  omega

