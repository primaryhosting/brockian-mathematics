import Mathlib

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
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

open Ordinal
open scoped NaturalOps

namespace Frontier

/-!
## Part 1: `ω ^ c` is principal for natural (Hessenberg) addition

Mathlib knows that `ω ^ c` is principal for ordinary ordinal addition, but not for the
natural sum `♯`.  We prove this here, since the ordinal assignment used for the hydra
game relies on it.
-/

/-- Every ordinal below `ω ^ d * ω` can be written as `ω ^ d * m + r` with `m` a natural
number and `r < ω ^ d`. -/

theorem nadd_lt_opow_omega0 (c : Ordinal) :
    ∀ a b : Ordinal, a < ω ^ c → b < ω ^ c → a ♯ b < ω ^ c := by
  induction c using Ordinal.induction with
  | _ c IH =>
  rcases Ordinal.zero_or_succ_or_isSuccLimit c with rfl | ⟨d, rfl⟩ | hlim
  · intro a b ha hb
    rw [Ordinal.opow_zero, Ordinal.lt_one_iff_zero] at ha hb
    subst ha; subst hb
    simp
  · intro a b ha hb
    rw [Ordinal.opow_succ] at *
    obtain ⟨m, r, hr, rfl⟩ := exists_decomp d a ha
    obtain ⟨n, s, hs, rfl⟩ := exists_decomp d b hb
    have hd : ∀ x y : Ordinal, x < ω ^ d → y < ω ^ d → x ♯ y < ω ^ d :=
      IH d (Order.lt_succ_of_le le_rfl)
    exact (nadd_decomp_le d hd _ _ m n r s hr hs rfl rfl).trans_lt
      (opow_mul_nat_add_lt d (m + n) _ (hd _ _ hr hs))
  · intro a b ha hb
    obtain ⟨d, hd, had⟩ := (Ordinal.lt_opow_of_isSuccLimit (omega0_pos).ne' hlim).1 ha
    obtain ⟨e, he, hbe⟩ := (Ordinal.lt_opow_of_isSuccLimit (omega0_pos).ne' hlim).1 hb
    have h1 : a < ω ^ (max d e) :=
      had.trans_le (Ordinal.opow_le_opow_right omega0_pos (le_max_left d e))
    have h2 : b < ω ^ (max d e) :=
      hbe.trans_le (Ordinal.opow_le_opow_right omega0_pos (le_max_right d e))
    have hlt : max d e < c := max_lt hd he
    exact (IH _ hlt a b h1 h2).trans ((Ordinal.opow_lt_opow_iff_right one_lt_omega0).2 hlt)

/-!
## Part 2: Hydras and the Kirby–Paris game
-/

/-- A hydra is a finite rooted tree: a node carries the (ordered) list of its subtrees.
A *head* of the hydra is a leaf, i.e. a subtree of the form `Hydra.node []`. -/
inductive Hydra : Type
  | node : List Hydra → Hydra

namespace Hydra

-- The ordinal value of a hydra: the natural sum of `ω ^ (value of child)` over its
-- children, defined simultaneously with its list version.
mutual
/-- The ordinal value of a hydra: `Σ♯ ω ^ (value of child)`, a natural (Hessenberg) sum. -/
