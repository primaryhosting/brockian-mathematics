/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Polynomial

namespace Chem

/-- A primitive 11-th root of unity. -/

theorem C11fourier_mul_adj :
    C11fourier * C11adj = Matrix.diagonal (fun k => ((C11eig k : ℝ) : ℂ)) * C11fourier := by
  ext k j
  rw [Matrix.mul_apply, Matrix.diagonal_mul]
  have hpt : ∀ i : Fin 11, C11fourier k i * C11adj i j
      = (if i = j - 1 then zeta11 ^ ((k : ℕ) * (i : ℕ)) else 0)
        + (if i = j + 1 then zeta11 ^ ((k : ℕ) * (i : ℕ)) else 0) := by
    intro i
    rw [C11adj_apply, C11fourier_apply]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (j - 1) (fun i => zeta11 ^ ((k : ℕ) * (i : ℕ))),
    Finset.sum_ite_eq' Finset.univ (j + 1) (fun i => zeta11 ^ ((k : ℕ) * (i : ℕ)))]
  simp only [Finset.mem_univ, if_true]
  have hm : ((j - 1 : Fin 11) : ℕ) = (j.val + 10) % 11 := by simp [Fin.sub_def]; omega
  have hp : ((j + 1 : Fin 11) : ℕ) = (j.val + 1) % 11 := by simp [Fin.add_def]
  have e1 : zeta11 ^ ((k : ℕ) * ((j - 1 : Fin 11) : ℕ)) = zeta11 ^ ((k : ℕ) * (j.val + 10)) := by
    apply zeta11_pow_congr
    rw [hm]
    simp [Nat.mul_mod]
  have e2 : zeta11 ^ ((k : ℕ) * ((j + 1 : Fin 11) : ℕ)) = zeta11 ^ ((k : ℕ) * (j.val + 1)) := by
    apply zeta11_pow_congr
    rw [hp]
    simp [Nat.mul_mod]
  rw [e1, e2, show (k : ℕ) * (j.val + 10) = (k : ℕ) * j.val + 10 * (k : ℕ) by ring,
    show (k : ℕ) * (j.val + 1) = (k : ℕ) * j.val + (k : ℕ) by ring, pow_add, pow_add, C11eig]
  rw [← zeta11_pow_add_inv (k : ℕ)]
  push_cast
  ring

