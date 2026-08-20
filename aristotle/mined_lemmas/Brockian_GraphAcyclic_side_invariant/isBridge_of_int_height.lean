import Mathlib
namespace Brockian.GraphAcyclic

/-- Twin-admissible residue: both a and a+2 are units mod n. -/

lemma isBridge_of_int_height (g : V → ℤ) (hinj : Function.Injective g)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → g y = g x + 1 ∨ g y = g x - 1)
    {a b : V} (hab : G.Adj a b) (h1 : g b = g a + 1) : G.IsBridge s(a, b) := by
  refine ⟨hab, ?_⟩
  rintro ⟨p⟩
  -- `p` is a walk from `a` to `b` in `G` with the edge `s(a, b)` deleted
  have hp : s(a, b) ∉ p.edges := by
    intro he
    obtain ⟨d, -, hd_edge⟩ := List.mem_map.mp he
    have hd_edge_set : d.edge ∈ (G \ fromEdgeSet {s(a, b)}).edgeSet := d.edge_mem
    simp only [edgeSet_sdiff, edgeSet_fromEdgeSet, Set.mem_diff] at hd_edge_set
    simp [hd_edge, Sym2.isDiag_iff_proj_eq, hab.ne] at hd_edge_set
  have hstep_sub : ∀ ⦃u v : V⦄, (G \ fromEdgeSet {s(a, b)}).Adj u v →
      g v = g u + 1 ∨ g v = g u - 1 := fun _ _ hadj => hstep hadj.1
  have := side_invariant g hinj h1 hstep_sub p hp
  simp only [le_refl, true_iff] at this
  linarith [this]

/-- A graph admitting an injective `ℤ`-valued height function such that adjacent vertices have
heights differing by exactly one is acyclic. -/
