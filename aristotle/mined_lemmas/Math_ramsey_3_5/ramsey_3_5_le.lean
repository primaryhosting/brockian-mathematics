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

lemma ramsey_3_5_le (hs : 14 ≤ s.card) : CliqueOn G s 3 ∨ IndepOn G s 5 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h3, h5⟩ := hcon
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hne
  have hNi : G.IsIndepSet ((nbrs G s v : Finset V) : Set V) := isIndepSet_nbrs hv h3
  have hNcard : (nbrs G s v).card ≤ 4 := by
    by_contra hc
    exact h5 (indepOn_of_indep nbrs_subset hNi (by omega))
  have hsum := card_nbrs_add_card_nonnbrs (G := G) (s := s) hv
  have hM : 9 ≤ (nonnbrs G s v).card := by omega
  rcases ramsey_3_4_le (G := G) (s := nonnbrs G s v) hM with hcl | hind
  · exact h3 (hcl.mono nonnbrs_subset)
  · obtain ⟨B, hB, hBcard, hBind⟩ := hind
    have := indepOn_insert hv hB hBind
    rw [hBcard] at this
    exact h5 this

end Bounds

/-! ## The Ramsey property and the Ramsey number -/

/-- `RamseyArrow n p q` says that every graph on `n` vertices contains either a clique with
`p` vertices or an independent set with `q` vertices. -/
