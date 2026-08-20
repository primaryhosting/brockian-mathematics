import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-- The `N × N` discrete Fourier transform (QFT) matrix:
`(QFT)_{j,k} = (1/√N) · exp(2πi·j·k/N)`. -/

lemma qftRoot_sum (N : ℕ) (hN : N ≠ 0) (j k : Fin N) :
    ∑ l : Fin N, star ((qftRoot N) ^ ((l : ℕ) * (j : ℕ))) * (qftRoot N) ^ ((l : ℕ) * (k : ℕ))
      = if j = k then (N : ℂ) else 0 := by
  set w := qftRoot N with hw
  have hprim : IsPrimitiveRoot w N := qftRoot_isPrimitiveRoot N hN
  have hwne : w ≠ 0 := qftRoot_ne_zero N
  set z : ℂ := (w⁻¹) ^ (j : ℕ) * w ^ (k : ℕ) with hz
  have hterm : ∀ l : Fin N,
      star (w ^ ((l : ℕ) * (j : ℕ))) * w ^ ((l : ℕ) * (k : ℕ)) = z ^ (l : ℕ) := by
    intro l
    rw [star_pow, star_qftRoot N, ← hw, hz, mul_pow, ← pow_mul, ← pow_mul,
      mul_comm (j : ℕ) (l : ℕ), mul_comm (k : ℕ) (l : ℕ)]
  rw [Finset.sum_congr rfl (fun l _ => hterm l)]
  rw [Fin.sum_univ_eq_sum_range (fun i => z ^ i) N]
  by_cases hjk : j = k
  · subst hjk
    have : z = 1 := by
      rw [hz, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hwne)]
    simp [this]
  · have hz1 : z ≠ 1 := by
      intro h
      apply hjk
      rw [hz, inv_pow, inv_mul_eq_one₀ (pow_ne_zero _ hwne)] at h
      exact Fin.val_injective (hprim.pow_inj j.isLt k.isLt h)
    have hzN : z ^ N = 1 := by
      rw [hz, mul_pow, ← pow_mul, ← pow_mul, mul_comm (j : ℕ) N, mul_comm (k : ℕ) N,
        pow_mul, pow_mul, inv_pow, hprim.pow_eq_one]
      simp
    rw [geom_sum_eq hz1, hzN, sub_self, zero_div, if_neg hjk]

