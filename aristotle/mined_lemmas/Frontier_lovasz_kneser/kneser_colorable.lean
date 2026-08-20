import Mathlib

/-!
# Covering the pairs of a finite set by intersecting families

This file contains the combinatorial core of the case `k = 2` of the Lovász–Kneser theorem.

A proper colouring of the Kneser graph `KG_{n,2}` is exactly a partition of the `2`-element
subsets of an `n`-element set into *intersecting families*.  Such a family is either contained
in a "star" (all its members share a common element) or is a "triangle" (and then has exactly
three members).  This dichotomy drives an induction showing that at least `n - 2` families are
needed.
-/

namespace Frontier

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- A two-element finset containing `x` is `{x, y}` for some `y ≠ x`. -/

theorem kneser_colorable (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (KneserGraph n k).Colorable (n - 2 * k + 2) := by
  classical
  have hne : ∀ a : KneserVertex n k, (a : Finset (Fin n)).Nonempty := by
    intro a
    rw [← Finset.card_pos, a.2]
    omega
  set N : ℕ := n - 2 * k + 1 with hN
  have hNlt : N < n := by omega
  set c : Fin n := ⟨N, hNlt⟩ with hcdef
  have hc : (c : ℕ) = n - 2 * k + 1 := rfl
  -- colour a set by the minimum of (the value of) its least element and `N`
  refine ⟨SimpleGraph.Coloring.mk
    (fun a => (⟨min ((a : Finset (Fin n)).min' (hne a) : ℕ) N, by omega⟩ :
      Fin (n - 2 * k + 2))) ?_⟩
  rintro a b ⟨hab, hd⟩ hcol
  simp only [Fin.mk.injEq] at hcol
  set x : ℕ := ((a : Finset (Fin n)).min' (hne a) : ℕ) with hx
  set y : ℕ := ((b : Finset (Fin n)).min' (hne b) : ℕ) with hy
  by_cases hlt : min x N < N
  · -- both sets have the same least element, hence share it
    have hxy : x = y := by omega
    have hmem : (a : Finset (Fin n)).min' (hne a) ∈ (b : Finset (Fin n)) := by
      have heq : (a : Finset (Fin n)).min' (hne a) = (b : Finset (Fin n)).min' (hne b) :=
        Fin.ext (by rw [← hx, ← hy, hxy])
      rw [heq]
      exact Finset.min'_mem _ _
    exact (Finset.disjoint_left.mp hd ((a : Finset (Fin n)).min'_mem (hne a))) hmem
  · -- both sets live in the last `2k - 1` elements
    have hxN : N ≤ x := by omega
    have hyN : N ≤ y := by omega
    refine not_disjoint_of_tail c hc _ _ a.2 b.2 ?_ ?_ hd
    · intro i hi
      have h1 := Fin.le_def.mp (Finset.min'_le (a : Finset (Fin n)) i hi)
      exact Finset.mem_Ici.mpr (Fin.le_def.mpr (by omega))
    · intro i hi
      have h1 := Fin.le_def.mp (Finset.min'_le (b : Finset (Fin n)) i hi)
      exact Finset.mem_Ici.mpr (Fin.le_def.mpr (by omega))

