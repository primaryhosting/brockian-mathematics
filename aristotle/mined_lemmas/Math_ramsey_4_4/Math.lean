import Mathlib
/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

open scoped Classical

namespace Ramsey44

variable {V : Type*}

/-- `Arr G s p q` says that inside the vertex set `s` there is either a `p`-clique of `G`
or a `q`-clique of the complement of `G` (i.e. an independent set of size `q`). -/

theorem Math.ramsey_4_4 :
    IsLeast {N : ℕ | ∀ G : SimpleGraph (Fin N),
      (∃ s : Finset (Fin N), G.IsNClique 4 s) ∨ (∃ s : Finset (Fin N), Gᶜ.IsNClique 4 s)} 18 := by
  constructor
  · intro G
    rcases arr_44 (s := (Finset.univ : Finset (Fin 18))) (G := G) (by simp) with
      ⟨t, _, ht⟩ | ⟨t, _, ht⟩
    · exact Or.inl ⟨t, ht⟩
    · exact Or.inr ⟨t, ht⟩
  · intro N hN
    by_contra hlt
    have hN17 : N ≤ 17 := by omega
    have := ramseyProp_mono hN17 hN
    rcases this paley with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact paley_cliqueFree s hs
    · exact paley_compl_cliqueFree s hs

