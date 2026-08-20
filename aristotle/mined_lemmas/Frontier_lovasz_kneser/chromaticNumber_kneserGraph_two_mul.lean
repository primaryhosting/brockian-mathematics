/-
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is
-- repeated as the module docstring immediately after the import.)

import Mathlib

/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset SimpleGraph

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of an `n`-element set,
two of them being adjacent when they are disjoint.  (For `k ≥ 1` disjointness already forces
the two vertices to be distinct; the explicit `s ≠ t` only serves to make the relation
irreflexive in the degenerate case `k = 0`.) -/

theorem chromaticNumber_kneserGraph_two_mul (k : ℕ) (hk : 1 ≤ k) :
    (kneserGraph (2 * k) k).chromaticNumber = 2 := by
  have hpos : 0 < 2 * k := by omega
  set z : Fin (2 * k) := ⟨0, hpos⟩ with hz
  -- two adjacent vertices are complementary, so their union is everything
  have hunion : ∀ s t : KneserVertex (2 * k) k, (kneserGraph (2 * k) k).Adj s t →
      (s : Finset (Fin (2 * k))) ∪ (t : Finset (Fin (2 * k))) = Finset.univ := by
    intro s t h
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint h.2, s.2, t.2, Fintype.card_fin]
    omega
  -- colour a vertex according to whether it contains the element `0`
  have hcol : (kneserGraph (2 * k) k).Colorable 2 := by
    refine ⟨SimpleGraph.Coloring.mk
      (fun s => if z ∈ (s : Finset (Fin (2 * k))) then 0 else 1) ?_⟩
    intro s t h
    have hu := hunion s t h
    have hz' : z ∈ (s : Finset (Fin (2 * k))) ∪ (t : Finset (Fin (2 * k))) := by
      rw [hu]; exact Finset.mem_univ _
    rcases Finset.mem_union.1 hz' with h1 | h1
    · have h2 : z ∉ (t : Finset (Fin (2 * k))) := Finset.disjoint_left.1 h.2 h1
      simp [h1, h2]
    · have h2 : z ∉ (s : Finset (Fin (2 * k))) := Finset.disjoint_right.1 h.2 h1
      simp [h1, h2]
  -- the graph does have an edge, so one colour is not enough
  have hkl : k < 2 * k := by omega
  set a : Fin (2 * k) := ⟨k, hkl⟩ with ha
  have hs : (Finset.Iio a).card = k := by simp [ha]
  have ht : (Finset.Ici a).card = k := by simp [ha]; omega
  set S : KneserVertex (2 * k) k := ⟨Finset.Iio a, hs⟩ with hS
  set T : KneserVertex (2 * k) k := ⟨Finset.Ici a, ht⟩ with hT
  have hdisj : Disjoint (Finset.Iio a) (Finset.Ici a) := by
    simp [Finset.disjoint_left]
  have hne : S ≠ T := by
    intro h
    have h' : (Finset.Iio a) = Finset.Ici a := congrArg Subtype.val h
    rw [h'] at hdisj
    have he := disjoint_self.1 hdisj
    rw [he] at ht
    simp at ht
    omega
  have hadj : (kneserGraph (2 * k) k).Adj S T := ⟨hne, hdisj⟩
  have hlb : ¬ (kneserGraph (2 * k) k).Colorable 1 := by
    rintro ⟨C⟩
    exact C.valid hadj (Subsingleton.elim _ _)
  have h1 : (kneserGraph (2 * k) k).chromaticNumber ≤ 2 :=
    SimpleGraph.chromaticNumber_le_iff_colorable.2 hcol
  have h2 : ¬ (kneserGraph (2 * k) k).chromaticNumber ≤ 1 := fun h =>
    hlb (SimpleGraph.chromaticNumber_le_iff_colorable.1 (by exact_mod_cast h))
  exact le_antisymm h1 (Order.add_one_le_of_lt (not_le.1 h2))

/-! ### The base case `n = 2k + 1`: `KG_{2k+1,k}` is the odd graph `O_{k+1}` -/

/-- The cyclic interval `{i, i+1, …, i+k-1}` of `Fin (2k+1)`, indices taken modulo `2k+1`. -/
