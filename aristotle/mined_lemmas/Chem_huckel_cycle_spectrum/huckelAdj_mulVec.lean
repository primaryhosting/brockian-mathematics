import Mathlib
/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
In Hückel molecular orbital theory the π-energies of an annulene `C_n H_n` are `α + β λ`,
where `λ` runs over the eigenvalues of the adjacency matrix of the cycle graph `C n`.
This file proves that this spectrum is exactly `{2 cos (2 π k / n) : k = 0, …, n-1}`.

The proof diagonalizes the (circulant) adjacency matrix by the Vandermonde/Fourier matrix
built from the `n`-th roots of unity.
-/

open scoped BigOperators Real

namespace Chem

open SimpleGraph Matrix Complex

/-- The Hückel (adjacency) matrix of the cycle graph `C n`, with entries in `ℂ`:
the `(i, j)` entry is `1` when `i` and `j` are adjacent in `C n`, and `0` otherwise. -/

theorem huckelAdj_mulVec (hn : 3 ≤ n) (k : Fin n) :
    (huckelAdj n).mulVec (fun j : Fin n => (omegaC n) ^ (k.val * j.val))
      = fun j : Fin n =>
        ((2 * Real.cos (2 * Real.pi * k.val / n) : ℝ) : ℂ) * (omegaC n) ^ (k.val * j.val) := by
  have hn0 : n ≠ 0 := by omega
  have hω : (omegaC n) ^ n = 1 := omegaC_pow_n hn0
  set ζ : ℂ := (omegaC n) ^ k.val with hζdef
  have hζn : ζ ^ n = 1 := by
    rw [hζdef, ← pow_mul, mul_comm, pow_mul, hω, one_pow]
  have hpow : ∀ j : Fin n, (omegaC n) ^ (k.val * j.val) = ζ ^ j.val := by
    intro j; rw [hζdef, ← pow_mul]
  have hone : ((1 : Fin n)).val = 1 := by
    have : (1 : Fin n).val = 1 % n := rfl
    rw [this, Nat.mod_eq_of_lt (by omega)]
  have hneg : ((-1 : Fin n)).val = n - 1 := by
    have : ((-1 : Fin n)).val = (n - (1 : Fin n).val) % n := rfl
    rw [this, hone, Nat.mod_eq_of_lt (by omega)]
  have hinv : ζ ^ (n - 1) = ζ⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ]
    have : n - 1 + 1 = n := by omega
    rw [this, hζn]
  funext i
  simp only [Matrix.mulVec, dotProduct, huckelAdj]
  rw [sum_adj_eq hn i (fun j => (omegaC n) ^ (k.val * j.val))]
  simp only [hpow]
  rw [sub_eq_add_neg, pow_val_add hζn i (-1), pow_val_add hζn i 1, hone, hneg, hinv, pow_one]
  have hcos := omegaC_pow_add_inv (n := n) hn0 k.val
  rw [← hζdef] at hcos
  rw [show ζ ^ i.val * ζ⁻¹ + ζ ^ i.val * ζ = (ζ + ζ⁻¹) * ζ ^ i.val by ring, hcos]

omit [NeZero n] in
