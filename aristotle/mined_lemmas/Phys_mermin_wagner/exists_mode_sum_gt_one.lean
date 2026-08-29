/-
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Real

namespace Phys

/-- The spin-wave (harmonic) energy of the Fourier mode `j` of a nearest-neighbour
model on the `d`-dimensional discrete torus with `L` sites per side, in units where
the coupling constant is `1`.  The momentum attached to the mode `j` has components
`k i = 2π * j i / L`, and the lattice dispersion relation is
`ε k = ∑ i, 2 * (1 - cos (k i))`. -/

lemma exists_mode_sum_gt_one (B : ℝ) :
    ∃ (L : ℕ) (D : Finset (Fin 1 → Fin L)),
      (∀ j ∈ D, ∃ i, (j i : ℕ) ≠ 0) ∧
      B * (L : ℝ) ^ (1 : ℕ) < ∑ j ∈ D, 1 / modeSq 1 L j := by
  set L : ℕ := ⌈4 * π ^ 2 * B⌉₊ + 2 with hL
  have hL2 : 2 ≤ L := by omega
  have hLR : (0:ℝ) < (L:ℝ) := by positivity
  have hBL : 4 * π ^ 2 * B < (L:ℝ) := by
    have h1 : ((⌈4 * π ^ 2 * B⌉₊ : ℕ) : ℝ) + 2 = (L:ℝ) := by
      rw [hL]; push_cast; ring
    linarith [Nat.le_ceil (4 * π ^ 2 * B)]
  refine ⟨L, {fun _ => (⟨1, by omega⟩ : Fin L)}, ?_, ?_⟩
  · intro j hj
    simp only [Finset.mem_singleton] at hj
    refine ⟨0, ?_⟩
    simp [hj]
    omega
  · rw [Finset.sum_singleton]
    have hq : modeSq 1 L (fun _ => (⟨1, by omega⟩ : Fin L)) = 4 * π ^ 2 / (L:ℝ) ^ 2 := by
      simp [modeSq]
      ring
    rw [hq, one_div_div, pow_one, lt_div_iff₀ (by positivity)]
    nlinarith [hLR, hBL, Real.pi_pos]

/-- Rewriting a sum over the "triangular" set of two-dimensional modes
`{0 < j 0 ≤ j 1}` as an iterated sum. -/
