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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open SimpleGraph Finset

/-- `RamseyProp n k l` says that every simple graph on `n` vertices contains either a clique
of size `k` or an independent set (a clique of its complement) of size `l`. -/

theorem ramsey_upper (G : SimpleGraph (Fin 9)) :
    (∃ s, G.IsNClique 3 s) ∨ (∃ s, Gᶜ.IsNClique 4 s) := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hc3, hc4⟩ := hcon
  have h3 : G.CliqueFree 3 := fun t ht => hc3 t ht
  have h4 : Gᶜ.CliqueFree 4 := fun t ht => hc4 t ht
  have hdeg : ∀ v : Fin 9, G.degree v = 3 := by
    intro v
    have h1 := degree_le_three h3 h4 v
    have h2 := three_le_degree h3 h4 v
    rw [SimpleGraph.degree] at *
    omega
  have hsum : ∑ v : Fin 9, G.degree v = 2 * G.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges G
  rw [Finset.sum_congr rfl (fun v _ => hdeg v)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

end Nine

/-! ### Transferring the `8`-vertex example to fewer vertices -/

