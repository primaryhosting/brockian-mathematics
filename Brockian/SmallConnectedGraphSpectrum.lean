import Brockian.GraphComponentMatrix
import Brockian.ConstellationSpectrum

/-!
# Spectra of connected graphs on at most three vertices

A connected simple graph on one or two vertices is respectively the one-vertex or two-vertex
path.  On three vertices, acyclicity is necessary: without it the graph may be a triangle.  This
module proves the corresponding characteristic-polynomial classification for the shifted
adjacency matrix `2I - A` without choosing labels for the vertices.
-/

namespace Brockian.SmallConnectedGraphSpectrum

open Matrix Polynomial SimpleGraph
open Brockian.GraphComponentMatrix
open Brockian.ConstellationSpectrum

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Every simple graph on one vertex is isomorphic to the one-vertex path graph. -/
theorem nonempty_iso_pathGraph_one (G : SimpleGraph V)
    (hcard : Fintype.card V = 1) :
    Nonempty (G ≃g SimpleGraph.pathGraph 1) := by
  let e : V ≃ Fin 1 := Fintype.equivFinOfCardEq hcard
  let G' : SimpleGraph (Fin 1) := G.comap e.symm
  have hgraph : G' = SimpleGraph.pathGraph 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [G', SimpleGraph.pathGraph_adj]
  have f : G ≃g G' := (SimpleGraph.Iso.comap e.symm G).symm
  rw [hgraph] at f
  exact ⟨f⟩

/-- Every connected simple graph on two vertices is isomorphic to the two-vertex path graph. -/
theorem nonempty_iso_pathGraph_two (G : SimpleGraph V)
    (hconn : G.Connected) (hcard : Fintype.card V = 2) :
    Nonempty (G ≃g SimpleGraph.pathGraph 2) := by
  let e : V ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
  let G' : SimpleGraph (Fin 2) := G.comap e.symm
  have hconn' : G'.Connected :=
    (SimpleGraph.Iso.comap e.symm G).connected_iff.mpr hconn
  have hadj : G'.Adj 0 1 := by
    obtain ⟨u, hu⟩ := hconn'.preconnected.exists_adj_of_nontrivial (0 : Fin 2)
    fin_cases u
    · exact (hu.ne rfl).elim
    · exact hu
  have hgraph : G' = SimpleGraph.pathGraph 2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SimpleGraph.pathGraph_adj, hadj, hadj.symm]
  have f : G ≃g G' := (SimpleGraph.Iso.comap e.symm G).symm
  rw [hgraph] at f
  exact ⟨f⟩

/-- Every connected acyclic simple graph on three vertices is isomorphic to the three-vertex
path graph.  Acyclicity is necessary because the triangle is also connected and has three
vertices. -/
theorem nonempty_iso_pathGraph_three_of_acyclic (G : SimpleGraph V)
    (hconn : G.Connected) (hacyc : G.IsAcyclic) (hcard : Fintype.card V = 3) :
    Nonempty (G ≃g SimpleGraph.pathGraph 3) := by
  let e : V ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
  let G' : SimpleGraph (Fin 3) := G.comap e.symm
  have hconn' : G'.Connected :=
    (SimpleGraph.Iso.comap e.symm G).connected_iff.mpr hconn
  have hacyc' : G'.IsAcyclic :=
    (SimpleGraph.Iso.comap e.symm G).isAcyclic_iff.mpr hacyc
  have h0 : G'.Adj 0 1 ∨ G'.Adj 0 2 := by
    obtain ⟨u, hu⟩ := hconn'.preconnected.exists_adj_of_nontrivial (0 : Fin 3)
    fin_cases u
    · exact (hu.ne rfl).elim
    · exact Or.inl hu
    · exact Or.inr hu
  have h1 : G'.Adj 0 1 ∨ G'.Adj 1 2 := by
    obtain ⟨u, hu⟩ := hconn'.preconnected.exists_adj_of_nontrivial (1 : Fin 3)
    fin_cases u
    · exact Or.inl hu.symm
    · exact (hu.ne rfl).elim
    · exact Or.inr hu
  have h2 : G'.Adj 0 2 ∨ G'.Adj 1 2 := by
    obtain ⟨u, hu⟩ := hconn'.preconnected.exists_adj_of_nontrivial (2 : Fin 3)
    fin_cases u
    · exact Or.inl hu.symm
    · exact Or.inr hu.symm
    · exact (hu.ne rfl).elim
  have hnot : ¬ (G'.Adj 0 1 ∧ G'.Adj 0 2 ∧ G'.Adj 1 2) := by
    rintro ⟨h01, h02, h12⟩
    apply hacyc'.cliqueFree (n := 3) (by norm_num) Finset.univ
    constructor
    · intro a _ b _ hab
      fin_cases a <;> fin_cases b
      · exact (hab rfl).elim
      · exact h01
      · exact h02
      · exact h01.symm
      · exact (hab rfl).elim
      · exact h12
      · exact h02.symm
      · exact h12.symm
      · exact (hab rfl).elim
    · simp
  have base : G ≃g G' := (SimpleGraph.Iso.comap e.symm G).symm
  by_cases h01 : G'.Adj 0 1
  · by_cases h02 : G'.Adj 0 2
    · have hn12 : ¬ G'.Adj 1 2 := fun h12 => hnot ⟨h01, h02, h12⟩
      have hn21 : ¬ G'.Adj 2 1 := fun h => hn12 h.symm
      let p : Equiv.Perm (Fin 3) := Equiv.swap 0 1
      have hp0 : p 0 = 1 := Equiv.swap_apply_left 0 1
      have hp1 : p 1 = 0 := Equiv.swap_apply_right 0 1
      have hp2 : p 2 = 2 := Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
      let f : G' ≃g SimpleGraph.pathGraph 3 :=
        { toEquiv := p
          map_rel_iff' := by
            intro i j
            fin_cases i <;> fin_cases j <;>
              simp [hp0, hp1, hp2, SimpleGraph.pathGraph_adj, h01, h01.symm, h02,
                h02.symm, hn12, hn21] }
      exact ⟨base.trans f⟩
    · have h12 : G'.Adj 1 2 := h2.resolve_left h02
      have hn20 : ¬ G'.Adj 2 0 := fun h => h02 h.symm
      let f : G' ≃g SimpleGraph.pathGraph 3 :=
        { toEquiv := Equiv.refl _
          map_rel_iff' := by
            intro i j
            fin_cases i <;> fin_cases j <;>
              simp [SimpleGraph.pathGraph_adj, h01, h01.symm, h02, hn20, h12, h12.symm] }
      exact ⟨base.trans f⟩
  · have h02 : G'.Adj 0 2 := h0.resolve_left h01
    have h12 : G'.Adj 1 2 := h1.resolve_left h01
    have hn10 : ¬ G'.Adj 1 0 := fun h => h01 h.symm
    let p : Equiv.Perm (Fin 3) := Equiv.swap 1 2
    have hp0 : p 0 = 0 := Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
    have hp1 : p 1 = 2 := Equiv.swap_apply_left 1 2
    have hp2 : p 2 = 1 := Equiv.swap_apply_right 1 2
    let f : G' ≃g SimpleGraph.pathGraph 3 :=
      { toEquiv := p
        map_rel_iff' := by
          intro i j
          fin_cases i <;> fin_cases j <;>
            simp [hp0, hp1, hp2, SimpleGraph.pathGraph_adj, h01, hn10, h02, h02.symm,
              h12, h12.symm] }
    exact ⟨base.trans f⟩

/-- Reindexing a shifted adjacency matrix along a vertex equivalence does not change its
characteristic polynomial. -/
theorem shiftedAdjacency_charpoly_reindex (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (e : V ≃ Fin n) :
    (Matrix.reindex e e (shiftedAdjacency G (2 : ℝ))).charpoly =
      (shiftedAdjacency G (2 : ℝ)).charpoly :=
  Matrix.charpoly_reindex e _

/-- A one-vertex simple graph has the `H1` characteristic polynomial. -/
theorem shiftedAdjacency_charpoly_card_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 1) :
    (shiftedAdjacency G (2 : ℝ)).charpoly = H1.charpoly := by
  let e : V ≃ Fin 1 := Fintype.equivFinOfCardEq hcard
  rw [← shiftedAdjacency_charpoly_reindex G e]
  congr 1
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.reindex_apply, shiftedAdjacency, SimpleGraph.adjMatrix_apply, H1]

/-- A connected two-vertex simple graph has the `H2` characteristic polynomial. -/
theorem shiftedAdjacency_charpoly_card_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hcard : Fintype.card V = 2) :
    (shiftedAdjacency G (2 : ℝ)).charpoly = H2.charpoly := by
  let e : V ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
  let G' : SimpleGraph (Fin 2) := G.comap e.symm
  have hconn' : G'.Connected :=
    (SimpleGraph.Iso.comap e.symm G).connected_iff.mpr hconn
  have hadj' : G'.Adj 0 1 := by
    obtain ⟨u, hu⟩ := hconn'.preconnected.exists_adj_of_nontrivial (0 : Fin 2)
    fin_cases u
    · exact (hu.ne rfl).elim
    · exact hu
  have hadj : G.Adj (e.symm 0) (e.symm 1) := hadj'
  rw [← shiftedAdjacency_charpoly_reindex G e]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindex_apply, shiftedAdjacency, SimpleGraph.adjMatrix_apply, H2, hadj,
      hadj.symm]

/-- A connected acyclic three-vertex simple graph has the `H3` characteristic polynomial.

The acyclicity assumption is sharp: the connected triangle has three vertices but a different
characteristic polynomial.
-/
theorem shiftedAdjacency_charpoly_card_three_of_acyclic
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hacyc : G.IsAcyclic) (hcard : Fintype.card V = 3) :
    (shiftedAdjacency G (2 : ℝ)).charpoly = H3.charpoly := by
  let e : V ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
  let G' : SimpleGraph (Fin 3) := G.comap e.symm
  have hconn' : G'.Connected :=
    (SimpleGraph.Iso.comap e.symm G).connected_iff.mpr hconn
  have hacyc' : G'.IsAcyclic :=
    (SimpleGraph.Iso.comap e.symm G).isAcyclic_iff.mpr hacyc
  have h0 : G'.Adj 0 1 ∨ G'.Adj 0 2 := by
    obtain ⟨u, hu⟩ := hconn'.preconnected.exists_adj_of_nontrivial (0 : Fin 3)
    fin_cases u
    · exact (hu.ne rfl).elim
    · exact Or.inl hu
    · exact Or.inr hu
  have h1 : G'.Adj 0 1 ∨ G'.Adj 1 2 := by
    obtain ⟨u, hu⟩ := hconn'.preconnected.exists_adj_of_nontrivial (1 : Fin 3)
    fin_cases u
    · exact Or.inl hu.symm
    · exact (hu.ne rfl).elim
    · exact Or.inr hu
  have h2 : G'.Adj 0 2 ∨ G'.Adj 1 2 := by
    obtain ⟨u, hu⟩ := hconn'.preconnected.exists_adj_of_nontrivial (2 : Fin 3)
    fin_cases u
    · exact Or.inl hu.symm
    · exact Or.inr hu.symm
    · exact (hu.ne rfl).elim
  have hnot : ¬ (G'.Adj 0 1 ∧ G'.Adj 0 2 ∧ G'.Adj 1 2) := by
    rintro ⟨h01, h02, h12⟩
    apply hacyc'.cliqueFree (n := 3) (by norm_num) Finset.univ
    constructor
    · intro a _ b _ hab
      fin_cases a <;> fin_cases b
      · exact (hab rfl).elim
      · exact h01
      · exact h02
      · exact h01.symm
      · exact (hab rfl).elim
      · exact h12
      · exact h02.symm
      · exact h12.symm
      · exact (hab rfl).elim
    · simp
  rw [← shiftedAdjacency_charpoly_reindex G e]
  by_cases h01 : G'.Adj 0 1
  · by_cases h02 : G'.Adj 0 2
    · have hn12 : ¬ G'.Adj 1 2 := fun h12 => hnot ⟨h01, h02, h12⟩
      have gh01 : G.Adj (e.symm 0) (e.symm 1) := h01
      have gh10 : G.Adj (e.symm 1) (e.symm 0) := gh01.symm
      have gh02 : G.Adj (e.symm 0) (e.symm 2) := h02
      have gh20 : G.Adj (e.symm 2) (e.symm 0) := gh02.symm
      have ghn12 : ¬ G.Adj (e.symm 1) (e.symm 2) := hn12
      have ghn21 : ¬ G.Adj (e.symm 2) (e.symm 1) := fun h => ghn12 h.symm
      have hmat :
          Matrix.reindex e e (shiftedAdjacency G (2 : ℝ)) =
            !![2, -1, -1; -1, 2, 0; -1, 0, 2] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.reindex_apply, shiftedAdjacency, SimpleGraph.adjMatrix_apply,
            gh01, gh10, gh02, gh20, ghn12, ghn21]
      rw [hmat, H3_charpoly, Matrix.charpoly, Matrix.det_fin_three]
      simp only [Matrix.charmatrix_apply, Matrix.diagonal_apply, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, Matrix.head_fin_const, Fin.reduceEq, ↓reduceIte,
        map_neg, map_one, map_zero, map_ofNat, neg_zero, zero_sub, sub_zero]
      ring
    · have h12 : G'.Adj 1 2 := h2.resolve_left h02
      have gh01 : G.Adj (e.symm 0) (e.symm 1) := h01
      have gh10 : G.Adj (e.symm 1) (e.symm 0) := gh01.symm
      have ghn02 : ¬ G.Adj (e.symm 0) (e.symm 2) := h02
      have ghn20 : ¬ G.Adj (e.symm 2) (e.symm 0) := fun h => ghn02 h.symm
      have gh12 : G.Adj (e.symm 1) (e.symm 2) := h12
      have gh21 : G.Adj (e.symm 2) (e.symm 1) := gh12.symm
      have hmat : Matrix.reindex e e (shiftedAdjacency G (2 : ℝ)) = H3 := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.reindex_apply, shiftedAdjacency, SimpleGraph.adjMatrix_apply, H3,
            gh01, gh10, ghn02, ghn20, gh12, gh21]
      rw [hmat]
  · have h02 : G'.Adj 0 2 := h0.resolve_left h01
    have h12 : G'.Adj 1 2 := h1.resolve_left h01
    have ghn01 : ¬ G.Adj (e.symm 0) (e.symm 1) := h01
    have ghn10 : ¬ G.Adj (e.symm 1) (e.symm 0) := fun h => ghn01 h.symm
    have gh02 : G.Adj (e.symm 0) (e.symm 2) := h02
    have gh20 : G.Adj (e.symm 2) (e.symm 0) := gh02.symm
    have gh12 : G.Adj (e.symm 1) (e.symm 2) := h12
    have gh21 : G.Adj (e.symm 2) (e.symm 1) := gh12.symm
    have hmat :
        Matrix.reindex e e (shiftedAdjacency G (2 : ℝ)) =
          !![2, 0, -1; 0, 2, -1; -1, -1, 2] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.reindex_apply, shiftedAdjacency, SimpleGraph.adjMatrix_apply,
          ghn01, ghn10, gh02, gh20, gh12, gh21]
    rw [hmat, H3_charpoly, Matrix.charpoly, Matrix.det_fin_three]
    simp only [Matrix.charmatrix_apply, Matrix.diagonal_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.head_fin_const, Fin.reduceEq, ↓reduceIte,
      map_neg, map_one, map_zero, map_ofNat, neg_zero, zero_sub, sub_zero]
    ring

end

end Brockian.SmallConnectedGraphSpectrum
