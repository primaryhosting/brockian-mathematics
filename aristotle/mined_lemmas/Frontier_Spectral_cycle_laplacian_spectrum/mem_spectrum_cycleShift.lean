import Mathlib

/-!
# Cycle Laplacian Spectrum
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Frontier.Spectral

open Complex Matrix Polynomial

/-- The cyclic shift matrix indexed by `ZMod n`: the circulant matrix whose `(i, j)` entry is `1`
exactly when `i - j = 1`. -/

lemma mem_spectrum_cycleShift (n : ℕ) [NeZero n] (hn : 2 ≤ n) {z : ℂ} (hz : z ^ n = 1) :
    z ∈ spectrum ℂ (cycleShift n) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hz0 : z ≠ 0 := by
    intro h; rw [h, zero_pow (by omega)] at hz; exact zero_ne_one hz
  have hwn : (z⁻¹) ^ n = 1 := by rw [inv_pow, hz, inv_one]
  set v : ZMod n → ℂ := fun j => (z⁻¹) ^ j.val with hvdef
  have hvm1 : v (-1) = z := by
    have h := pow_val_add (v := z⁻¹) hwn (-1) 1
    rw [neg_add_cancel, ZMod.val_zero, pow_zero, ZMod.val_one n, pow_one] at h
    field_simp at h
    simpa [hvdef, one_div] using h.symm
  have hshift : ∀ i : ZMod n, v (i - 1) = z * v i := by
    intro i
    have h := pow_val_add (v := z⁻¹) hwn i (-1)
    rw [show i + (-1 : ZMod n) = i - 1 by ring] at h
    calc v (i - 1) = z⁻¹ ^ i.val * z⁻¹ ^ ((-1 : ZMod n)).val := h
      _ = v i * v (-1) := rfl
      _ = z * v i := by rw [hvm1]; ring
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨v, ?_, ?_⟩
  · intro h
    have h0 : v 0 = 0 := by rw [h]; rfl
    simp [hvdef] at h0
  · funext i
    show ((algebraMap ℂ (Matrix (ZMod n) (ZMod n) ℂ) z - cycleShift n) *ᵥ v) i = 0
    simp only [cycleShift, Matrix.mulVec, dotProduct, Matrix.circulant_apply, Pi.single_apply,
      Matrix.algebraMap_matrix_apply, Matrix.sub_apply]
    have key : ∑ x, ((if i = x then z else 0) - if i - x = 1 then 1 else 0) * v x
        = z * v i - v (i - 1) := by
      simp only [sub_mul, ite_mul, zero_mul, one_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      congr 1
      rw [Finset.sum_eq_single (i - 1)]
      · simp
      · intro b _ hb
        rw [if_neg]
        intro h
        exact hb (by rw [← h]; ring)
      · intro h; exact absurd (Finset.mem_univ _) h
    have hfin : z * v i - v (i - 1) = 0 := by rw [hshift i, sub_self]
    exact key.trans hfin

/-- The spectrum of the cyclic shift matrix is the set of `n`-th roots of unity. -/
