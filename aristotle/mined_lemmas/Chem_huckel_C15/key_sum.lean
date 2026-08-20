/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Hückel model for the cyclic polyene `C₁₅` has Hamiltonian `α + β A`, where `A` is the
adjacency matrix of the cycle graph `C₁₅`.  We show that the spectrum of `A` is exactly
`{2 cos (2πk/15) : k = 0, …, 14}`, by explicitly diagonalizing `A` with the discrete
Fourier matrix.
-/

namespace Chem

open Complex Matrix SimpleGraph Finset

/-- A primitive 15-th root of unity. -/

lemma key_sum (j j' : Fin 15) :
    ∑ k : Fin 15, om ^ (j.val * k.val) * (om ^ (k.val * j'.val))⁻¹
      = if j = j' then (15 : ℂ) else 0 := by
  set z : ℂ := om ^ j.val * (om ^ j'.val)⁻¹ with hz
  have hterm : ∀ k : Fin 15, om ^ (j.val * k.val) * (om ^ (k.val * j'.val))⁻¹ = z ^ k.val := by
    intro k
    rw [hz, mul_pow, ← pow_mul, inv_pow, ← pow_mul, mul_comm j'.val k.val]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [Fin.sum_univ_eq_sum_range (fun i => z ^ i) 15]
  by_cases h : j = j'
  · subst h
    have hz1 : z = 1 := by
      rw [hz, ← div_eq_mul_inv]
      exact div_self (pow_ne_zero _ om_ne_zero)
    simp [hz1]
  · have hzne : z ≠ 1 := by
      rw [hz, ← div_eq_mul_inv]
      intro hc
      have hpow : om ^ j.val = om ^ j'.val :=
        (div_eq_one_iff_eq (pow_ne_zero _ om_ne_zero)).mp hc
      exact h (Fin.ext (om_primitiveRoot.pow_inj j.isLt j'.isLt hpow))
    have hz15 : z ^ 15 = 1 := by
      rw [hz, mul_pow, ← pow_mul, inv_pow, ← pow_mul, mul_comm j.val 15, mul_comm j'.val 15,
        pow_mul, pow_mul, om_pow_15, one_pow, one_pow]
      simp
    rw [geom_sum_eq hzne, hz15]
    simp [h]

