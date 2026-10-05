/-
The quantum period-finding subroutine: the state produced by the algorithm,
the measurement distribution of the first register, and the lower bound on the
probability of a "good" measurement outcome.
-/
import Mathlib
import RequestProject.Analysis

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 2000000

namespace QI

/-- The primitive `Q`-th root of unity `e^{2πi/Q}` used by the quantum Fourier transform. -/

theorem measProb_eq (m : ℕ) (hr : 0 < r) (hrQ : r ≤ Q)
    (hf : ∀ j k : ℕ, f j = f k ↔ j % r = k % r) :
    measProb Q f m = ((Q : ℝ)⁻¹) ^ 2 *
      ∑ k ∈ Finset.range r,
        ‖∑ l ∈ Finset.range (blockCount Q r k), (omega Q ^ (r * m)) ^ l‖ ^ 2 := by
  have hinj : Set.InjOn f ↑(Finset.range r) := by
    intro x hx y hy hxy
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    have := (hf x y).mp hxy
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  rw [measProb, image_range_eq f Q r hr hrQ hf, Finset.sum_image hinj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  have hinj2 : Set.InjOn (fun l => k + l * r) ↑(Finset.range (blockCount Q r k)) := by
    intro x _ y _ hxy
    simp only at hxy
    exact Nat.eq_of_mul_eq_mul_right hr (by omega)
  rw [qftAmp_eq, fiber_eq f Q r k hr hk hf, Finset.sum_image hinj2]
  have hterm : ∀ l : ℕ,
      omega Q ^ ((k + l * r) * m) = omega Q ^ (k * m) * (omega Q ^ (r * m)) ^ l := by
    intro l
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun l _ => hterm l), ← Finset.mul_sum, ← mul_assoc, norm_mul, norm_mul,
    mul_pow, mul_pow, norm_pow, norm_omega]
  simp

/-- **Key probability bound.**  If the measured value `m` is such that `r * m` is
within `r/2` of a multiple of `Q` (i.e. `m/Q` is within `1/(2Q)` of some `s/r`),
then `m` is observed with probability at least `1/(16 r)`. -/
