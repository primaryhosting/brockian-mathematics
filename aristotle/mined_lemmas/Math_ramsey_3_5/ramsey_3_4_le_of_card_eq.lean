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

lemma ramsey_3_4_le_of_card_eq (hs : s.card = 9) : CliqueOn G s 3 ∨ IndepOn G s 4 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h3, h4⟩ := hcon
  -- every vertex of `s` has exactly 3 neighbours in `s`
  have hdeg : ∀ v ∈ s, (nbrs G s v).card = 3 := by
    intro v hv
    have hNi : G.IsIndepSet ((nbrs G s v : Finset V) : Set V) := isIndepSet_nbrs hv h3
    have hle : (nbrs G s v).card ≤ 3 := by
      by_contra hc
      exact h4 (indepOn_of_indep nbrs_subset hNi (by omega))
    have hsum := card_nbrs_add_card_nonnbrs (G := G) (s := s) hv
    have hge : 3 ≤ (nbrs G s v).card := by
      by_contra hc
      have hM : 6 ≤ (nonnbrs G s v).card := by omega
      rcases ramsey_3_3_le (G := G) (s := nonnbrs G s v) hM with hcl | hind
      · exact h3 (hcl.mono nonnbrs_subset)
      · obtain ⟨B, hB, hBcard, hBind⟩ := hind
        have := indepOn_insert hv hB hBind
        rw [hBcard] at this
        exact h4 this
    omega
  have heven := even_sum_card_nbrs G s
  rw [Finset.sum_congr rfl hdeg, Finset.sum_const, hs] at heven
  simp only [smul_eq_mul] at heven
  obtain ⟨k, hk⟩ := heven
  omega

