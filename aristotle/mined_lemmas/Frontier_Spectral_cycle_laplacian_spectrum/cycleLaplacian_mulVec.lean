import Mathlib
/-!
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
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

set_option grind.warning false

namespace Frontier.Spectral

open Complex Matrix

/-- The graph Laplacian of the cycle graph `C n`, as the `n × n` circulant matrix with
diagonal `2` and `-1` on the two cyclic off-diagonals (indices are taken in `ZMod n`). -/

lemma cycleLaplacian_mulVec (hn : 3 ≤ n) (v : ZMod n → ℂ) (i : ZMod n) :
    (cycleLaplacian n *ᵥ v) i = 2 * v i - v (i + 1) - v (i - 1) := by
  have h1 : (1 : ZMod n) ≠ 0 := by
    haveI : Fact (1 < n) := ⟨by omega⟩
    exact one_ne_zero
  have h2 : (2 : ZMod n) ≠ 0 := by
    intro h
    have hc : ((2 : ℕ) : ZMod n) = 0 := by push_cast; exact h
    have h3 := ZMod.val_natCast (n := n) 2
    rw [hc, Nat.mod_eq_of_lt (show 2 < n by omega)] at h3
    simp at h3
  have hd1 : (i : ZMod n) ≠ i - 1 := fun h => h1 (by linear_combination h)
  have hd2 : (i : ZMod n) ≠ i + 1 := fun h => h1 (by linear_combination -h)
  have hd3 : (i : ZMod n) - 1 ≠ i + 1 := fun h => h2 (by linear_combination -h)
  have key : ∀ j : ZMod n, cycleLaplacian n i j =
      (if j = i then (2 : ℂ) else 0) + (if j = i + 1 then -1 else 0)
        + (if j = i - 1 then -1 else 0) := by
    intro j
    simp only [cycleLaplacian, Matrix.of_apply]
    have c0 : (i = j) ↔ (j = i) := eq_comm
    have c1 : (i = j + 1) ↔ (j = i - 1) :=
      ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩
    have c2 : (i = j - 1) ↔ (j = i + 1) :=
      ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩
    simp only [c0, c1, c2]
    split_ifs <;> simp_all
  rw [Matrix.mulVec]
  simp only [dotProduct, key, add_mul, ite_mul, zero_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq' Finset.univ, Finset.mem_univ, if_true]
  ring

/-- The discrete Fourier vector attached to an `n`-th root of unity `ζ` is an eigenvector of
the cycle Laplacian, with eigenvalue `2 - ζ - ζ⁻¹`. -/
