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

theorem not_ramseyProp_of_le_eight {n : ℕ} (hn : n ≤ 8) : ¬ RamseyProp n 3 4 := by
  classical
  intro h
  set f : Fin n ↪ Fin 8 := Fin.castLEEmb hn with hf
  set G : SimpleGraph (Fin n) := wagner.comap f with hG
  have hinj : Function.Injective f := f.injective
  have hcompl : Gᶜ = wagnerᶜ.comap f := by
    ext a b
    simp only [hG, SimpleGraph.compl_adj, SimpleGraph.comap_adj]
    constructor
    · rintro ⟨hab, hnadj⟩
      exact ⟨fun hc => hab (hinj hc), hnadj⟩
    · rintro ⟨hab, hnadj⟩
      exact ⟨fun hc => hab (congrArg f hc), hnadj⟩
  have h3 : G.CliqueFree 3 :=
    wagner_cliqueFree_three.comap (SimpleGraph.Embedding.comap f wagner)
  have h4 : Gᶜ.CliqueFree 4 := by
    rw [hcompl]
    exact wagner_compl_cliqueFree_four.comap (SimpleGraph.Embedding.comap f wagnerᶜ)
  rcases h G with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact h3 s hs
  · exact h4 s hs

/-- **The Ramsey number `R(3,4)` equals `9`**: nine is the least number of vertices `n` such
that every graph on `n` vertices contains a triangle or an independent set of size `4`. -/
