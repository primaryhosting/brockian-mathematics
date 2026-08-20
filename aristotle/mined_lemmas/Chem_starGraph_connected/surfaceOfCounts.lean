import Mathlib

/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open SimpleGraph

/-! ### Star graphs are trees

We need a supply of concrete finite trees in order to exhibit examples of the
structure defined below; the simplest such family is the star graph. -/

/-- The star graph on `V` centred at `c`: `a` and `b` are adjacent iff they are
distinct and one of them is the centre `c`. -/

noncomputable def surfaceOfCounts (v f : ℕ) (hv : 0 < v) (hf : 0 < f) : PolyhedralSurface :=
  haveI : NeZero v := ⟨hv.ne'⟩
  haveI : NeZero f := ⟨hf.ne'⟩
  { Vertex := Fin v
    Edge := Fin (v + f - 2)
    Face := Fin f
    primalTree := starGraph (⟨0, hv⟩ : Fin v)
    dualTree := starGraph (⟨0, hf⟩ : Fin f)
    primalTree_isTree := starGraph_isTree _
    dualTree_isTree := starGraph_isTree _
    edge_partition := by
      have h1 := starGraph_card_edgeSet (⟨0, hv⟩ : Fin v)
      have h2 := starGraph_card_edgeSet (⟨0, hf⟩ : Fin f)
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h1 h2 ⊢
      omega }

