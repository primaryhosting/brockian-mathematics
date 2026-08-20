import Mathlib

/-!
# Abstract machinery for paradoxical decompositions

This file develops the general theory needed for the Banach–Tarski paradox, on top of
Mathlib's `Equidecomp` (equidecompositions for a group action).
-/

open Set Function Pointwise

namespace BT

variable {X G H : Type*} [Nonempty X] [Group G] [MulAction G X]

/-- Build an equidecomposition out of a function which is a bijection from `A` to `B` and
moves every point of `A` by an element of a fixed finite set of group elements. -/

theorem paradoxical_cone {A : Set E} (h : Paradoxical O3 A) (hA : A ⊆ S2) :
    Paradoxical O3 (cone A) := by
  obtain ⟨f, g, hfs, hgs, hd, hft, hgt⟩ := h
  obtain ⟨f', hf1, hf2⟩ := exists_cone_equidecomp f (hfs.trans hA) (by rw [hft]; exact hA)
  obtain ⟨g', hg1, hg2⟩ := exists_cone_equidecomp g (hgs.trans hA) (by rw [hgt]; exact hA)
  refine ⟨f', g', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf1]; exact cone_mono hfs
  · rw [hg1]; exact cone_mono hgs
  · rw [hf1, hg1]; exact cone_disjoint hd
  · rw [hf2, hft]
  · rw [hg2, hgt]

end BT

import Mathlib

/-!
# Euclidean 3-space, the orthogonal group and the isometry group

Basic set-up used throughout the Banach–Tarski development: the space `E = ℝ³`,
the action of the orthogonal group `O3` of `3 × 3` matrices on it, the group `Isom`
of isometries of `E`, and the homomorphism `O3 →* Isom`.
-/

open Matrix Set Function

namespace BT

/-- Euclidean 3-space. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-- The group of orthogonal `3 × 3` real matrices. -/
abbrev O3 := Matrix.orthogonalGroup (Fin 3) ℝ

noncomputable instance : SMul O3 E where
  smul M x := WithLp.toLp 2 ((M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ WithLp.ofLp x)

