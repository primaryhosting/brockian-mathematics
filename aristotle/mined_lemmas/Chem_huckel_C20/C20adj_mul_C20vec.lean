/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix Finset

/-- The adjacency matrix of the cycle graph `C₂₀`, indexed by `Fin 20`
(whose addition is addition modulo `20`). -/

lemma C20adj_mul_C20vec : C20adj * C20vec = C20vec * Matrix.diagonal C20eig := by
  ext i k
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  have hsplit : ∀ j : Fin 20, C20adj i j * C20vec j k
      = (if j = i + 1 then zeta20 ^ (j.val * k.val) else 0)
        + (if j = i - 1 then zeta20 ^ (j.val * k.val) else 0) := by
    intro j
    rcases eq_or_ne j (i + 1) with h1 | h1
    · subst h1
      simp [C20adj, C20vec, Fin20_add_one_ne_sub_one i]
    · rcases eq_or_ne j (i - 1) with h2 | h2
      · subst h2
        simp [C20adj, C20vec, h1]
      · simp [C20adj, C20vec, h1, h2]
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq' Finset.univ, Finset.mem_univ, if_true]
  rw [zeta20_pow_add_one, zeta20_pow_sub_one, C20eig_eq, C20vec, Matrix.of_apply,
    show (i.val + 1) * k.val = i.val * k.val + k.val by ring,
    show (i.val + 19) * k.val = i.val * k.val + 19 * k.val by ring, pow_add, pow_add]
  ring

