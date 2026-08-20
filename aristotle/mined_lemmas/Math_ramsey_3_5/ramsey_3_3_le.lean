import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

/-! ## Cliques and independent sets inside a finite set of vertices -/

section General

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {s t : Finset V} {n : ℕ} {v : V}

/-- `CliqueOn G s n` : the vertex set `s` contains a clique of `G` with `n` vertices. -/

lemma ramsey_3_3_le (hs : 6 ≤ s.card) : CliqueOn G s 3 ∨ IndepOn G s 3 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h3, h3'⟩ := hcon
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hne
  have hNi : G.IsIndepSet ((nbrs G s v : Finset V) : Set V) := isIndepSet_nbrs hv h3
  have hNcard : (nbrs G s v).card ≤ 2 := by
    by_contra hc
    exact h3' (indepOn_of_indep nbrs_subset hNi (by omega))
  have hsum := card_nbrs_add_card_nonnbrs (G := G) (s := s) hv
  have hMcard : 3 ≤ (nonnbrs G s v).card := by omega
  -- the non-neighbourhood must be a clique
  have hMcl : G.IsClique ((nonnbrs G s v : Finset V) : Set V) := by
    intro x hx y hy hxy
    by_contra hadj
    have hsub : ({x, y} : Finset V) ⊆ nonnbrs G s v := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact_mod_cast hx
      · exact_mod_cast hy
    have hind : G.IsIndepSet ((({x, y} : Finset V) : Finset V) : Set V) := by
      intro a ha b hb hab
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
        Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact hadj
      · exact fun h => hadj h.symm
      · exact absurd rfl hab
    have hres := indepOn_insert hv hsub hind
    rw [Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton] at hres
    exact h3' hres
  exact h3 (cliqueOn_of_clique nonnbrs_subset hMcl hMcard)

