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

lemma F_mul_G : F * G = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have h : ∀ k : ZMod 17, F i k * G k j = zeta (k * (i - j)) / 17 := by
    intro k
    unfold F G
    rw [div_eq_mul_inv, ← mul_assoc, ← zeta_add]
    ring_nf
  rw [Finset.sum_congr rfl (fun k _ => h k), ← Finset.sum_div, zeta_sum]
  by_cases hij : i = j
  · subst hij; simp
  · have : i - j ≠ 0 := sub_ne_zero_of_ne hij
    simp [this, hij]

