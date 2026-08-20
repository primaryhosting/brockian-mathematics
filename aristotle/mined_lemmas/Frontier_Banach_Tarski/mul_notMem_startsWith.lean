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

lemma mul_notMem_startsWith {i : Fin 2} {h : FreeGroup (Fin 2)}
    (hh : h ∈ startsWith (i, false)) : FreeGroup.of i * h ∉ startsWith (i, true) := by
  have hw : h.toWord = (i, false) :: h.toWord.tail := by
    unfold FreeGroup.startsWith at hh
    simp only [Set.mem_setOf_eq] at hh
    match hl : h.toWord with
    | [] => simp [hl] at hh
    | x :: t => simp [hl] at hh; simp [hh]
  have hred : FreeGroup.IsReduced h.toWord := FreeGroup.isReduced_toWord
  have key : (FreeGroup.of i * h).toWord = h.toWord.tail := by
    rw [FreeGroup.toWord_mul, show (FreeGroup.of i).toWord = [(i, true)] from FreeGroup.toWord_of i,
      hw]
    simp only [List.cons_append, List.nil_append]
    rw [FreeGroup.reduce.cons,
      show FreeGroup.reduce ((i, false) :: h.toWord.tail) = (i, false) :: h.toWord.tail from
        (hw ▸ hred).reduce_eq]
    simp
  intro hc
  unfold FreeGroup.startsWith at hc
  simp only [Set.mem_setOf_eq, key] at hc
  match hl : h.toWord.tail with
  | [] => simp [hl] at hc
  | y :: t =>
      rw [hl] at hc
      simp at hc
      have hred' : FreeGroup.IsReduced ((i, false) :: y :: t) := by rw [← hl, ← hw]; exact hred
      have h2 := (FreeGroup.isReduced_cons_cons.mp hred').1
      rw [hc] at h2
      simp at h2

/-- A set on which a free group of rank two acts freely is paradoxical. -/
