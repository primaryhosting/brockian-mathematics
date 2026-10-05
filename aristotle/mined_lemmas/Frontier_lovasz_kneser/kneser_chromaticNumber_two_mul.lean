import Mathlib

/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of an `n`-element set,
and two of them are adjacent when they are disjoint. -/

theorem kneser_chromaticNumber_two_mul (k : ℕ) (hk : 1 ≤ k) :
    (kneserGraph (2 * k) k).chromaticNumber = 2 := by
  have h2k : 0 < 2 * k := by omega
  -- Upper bound: colour a `k`-set by whether it contains the point `0`.
  have hcol : (kneserGraph (2 * k) k).Colorable 2 := by
    refine ⟨SimpleGraph.Coloring.mk
      (fun v => if (⟨0, h2k⟩ : Fin (2 * k)) ∈ (v : Finset (Fin (2 * k))) then (0 : Fin 2) else 1)
      ?_⟩
    rintro v w ⟨-, hd⟩
    have hcard : ((v : Finset (Fin (2 * k))) ∪ (w : Finset (Fin (2 * k)))).card = 2 * k := by
      rw [Finset.card_union_of_disjoint hd, v.2, w.2]; ring
    have huniv : (v : Finset (Fin (2 * k))) ∪ (w : Finset (Fin (2 * k))) = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa using hcard)
    have hmem : (⟨0, h2k⟩ : Fin (2 * k)) ∈
        (v : Finset (Fin (2 * k))) ∪ (w : Finset (Fin (2 * k))) := by
      rw [huniv]; exact Finset.mem_univ _
    rw [Finset.mem_union] at hmem
    rcases hmem with h | h
    · have h' : (⟨0, h2k⟩ : Fin (2 * k)) ∉ (w : Finset (Fin (2 * k))) :=
        fun hw => (Finset.disjoint_left.mp hd h) hw
      simp [h, h']
    · have h' : (⟨0, h2k⟩ : Fin (2 * k)) ∉ (v : Finset (Fin (2 * k))) :=
        fun hv => (Finset.disjoint_left.mp hd hv) h
      simp [h, h']
  -- Lower bound: the graph contains an edge.
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin (2 * k)))) (n := k) (by simp; omega)
  have hsc : (sᶜ).card = k := by
    rw [Finset.card_compl, hs]; simp; omega
  obtain ⟨a, ha⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
  have hne : s ≠ sᶜ := by
    intro hcon
    exact (Finset.mem_compl.mp (hcon ▸ ha)) ha
  have hadj : (kneserGraph (2 * k) k).Adj ⟨s, hs⟩ ⟨sᶜ, hsc⟩ := ⟨hne, disjoint_compl_right⟩
  have hvw : (⟨s, hs⟩ : KneserVertex (2 * k) k) ≠ ⟨sᶜ, hsc⟩ :=
    fun h => hne (congrArg Subtype.val h)
  have hclique : (kneserGraph (2 * k) k).IsClique
      (↑({⟨s, hs⟩, ⟨sᶜ, hsc⟩} : Finset (KneserVertex (2 * k) k))) := by
    simp only [Finset.coe_insert, Finset.coe_singleton]
    exact SimpleGraph.isClique_pair.mpr (fun _ => hadj)
  have hlow := hclique.card_le_chromaticNumber
  rw [Finset.card_insert_of_notMem (by simpa using hvw), Finset.card_singleton] at hlow
  refine le_antisymm ?_ (by exact_mod_cast hlow)
  exact_mod_cast SimpleGraph.chromaticNumber_le_iff_colorable.mpr hcol

/-! ### The odd graphs `KG_{2k+1,k}`

These contain an odd cycle, given by the cyclically consecutive blocks of `k` residues,
which forces the chromatic number to be at least `3`. -/

/-- The residue of `m` modulo `2k+1`, as an element of `Fin (2k+1)`. -/
