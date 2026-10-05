import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to come before any other command
(including module doc comments), so the header comment above is placed immediately after
the single `import Mathlib` line; its text is otherwise verbatim.

Mathematical content: the adjacency matrix `C17` of the cycle graph on 17 vertices is the
circulant matrix `A i j = 1` iff `i - j = ±1` (indices in `ZMod 17`).  It is diagonalised by
the discrete Fourier matrix `F i k = ζ^{ik}` (`ζ = exp (2πi/17)`), with eigenvalues
`ζ^k + ζ^{-k} = 2 cos (2πk/17)`.  Hence `det (μ - A) = ∏ (μ - 2 cos (2πk/17))`, and the
spectrum is exactly the set of these 17 numbers.
-/

namespace Chem

open Complex Matrix

/-- A primitive 17-th root of unity. -/

lemma C17_mul_F : C17 * F = F * Matrix.diagonal lam := by
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hne : (i - 1 : ZMod 17) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 17) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  have hstep : ∀ j : ZMod 17, C17 i j * F j k
      = if j ∈ ({i - 1, i + 1} : Finset (ZMod 17)) then zeta (j * k) else 0 := by
    intro j
    unfold C17 F
    by_cases h1 : j = i - 1
    · subst h1; simp
    · by_cases h2 : j = i + 1
      · subst h2; simp
      · have hA : ¬ (i - j = 1 ∨ i - j = -1) := by
          rintro (h | h)
          · exact h1 (by linear_combination -h)
          · exact h2 (by linear_combination -h)
        simp [hA, h1, h2]
  rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_pair hne]
  rw [Finset.sum_eq_single k]
  · unfold F
    rw [Matrix.diagonal_apply_eq, ← zeta_add_zeta_neg k,
      show (i - 1) * k = i * k + (-k) by ring, show (i + 1) * k = i * k + k by ring,
      zeta_add, zeta_add]
    ring
  · intro b _ hb
    exact mul_eq_zero_of_right _ (Matrix.diagonal_apply_ne _ hb)
  · intro h; simp at h

