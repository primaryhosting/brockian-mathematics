/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace QI

/-- The `n`-bit state space, an `n`-dimensional vector space over `ZMod 2`. -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

/-- The `ZMod 2`-valued inner product `⟪y, x⟫ = ∑ i, y i * x i`. -/

theorem simon_interference {n : ℕ} (s y : Vec n) (f : Vec n → Vec n)
    (hf : ∀ x, f (x + s) = f x) (hy : ip y s ≠ 0) (z : Vec n) :
    ∑ x ∈ Finset.univ.filter (fun x => f x = z), chi (ip y x) = 0 := by
  have hys : ip y s = 1 := by revert hy; generalize ip y s = a; revert a; decide
  have hss : ∀ x : Vec n, x + s + s = x := by
    intro x; rw [add_assoc, vec_add_self, add_zero]
  set A := Finset.univ.filter (fun x => f x = z) with hA
  have hmemA : ∀ x, x ∈ A → x + s ∈ A := by
    intro x hx
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hf x]; exact hx
  have key : ∑ x ∈ A, chi (ip y x) = ∑ x ∈ A, -chi (ip y x) := by
    refine Finset.sum_nbij' (i := fun x => x + s) (j := fun x => x + s) ?_ ?_ ?_ ?_ ?_
    · intro a ha; exact hmemA a ha
    · intro b hb; exact hmemA b hb
    · intro a _; exact hss a
    · intro b _; exact hss b
    · intro a _
      rw [ip_add, hys, chi_add_one, neg_neg]
  rw [Finset.sum_neg_distrib] at key
  linarith

/-! ## Quantum side: `n` measurement outcomes determine the hidden shift -/

