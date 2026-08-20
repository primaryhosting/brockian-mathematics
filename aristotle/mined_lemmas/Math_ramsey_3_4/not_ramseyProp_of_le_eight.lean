/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

open Finset

/-- `RamseyProp n` says that every simple graph on `n` vertices contains either a triangle
(a 3-clique) or an independent set of size 4 (a 4-clique in the complement). -/

theorem not_ramseyProp_of_le_eight {n : ℕ} (hn : n ≤ 8) : ¬ RamseyProp n := by
  intro h
  set f : Fin n ↪ Fin 8 := Fin.castLEEmb hn with hf
  set H : SimpleGraph (Fin n) := SimpleGraph.comap f G8 with hH
  have hinj : Function.Injective f := f.injective
  have e1 : H ↪g G8 := SimpleGraph.Embedding.comap f G8
  have e2 : Hᶜ ↪g G8ᶜ := by
    refine ⟨f, ?_⟩
    intro a b
    simp only [SimpleGraph.compl_adj, hH, SimpleGraph.comap_adj]
    constructor
    · rintro ⟨hne, hadj⟩
      exact ⟨fun hab => hne (by rw [hab]), hadj⟩
    · rintro ⟨hne, hadj⟩
      exact ⟨fun hab => hne (hinj hab), hadj⟩
  rcases h H with hc | hc
  · exact hc (G8_cliqueFree_three.comap e1)
  · exact hc (G8_compl_cliqueFree_four.comap e2)

/-- **R(3,4) = 9**: nine is the least number of vertices forcing a triangle or an
independent set of size four. -/
