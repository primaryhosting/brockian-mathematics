import Mathlib

open Finset Polynomial ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace Math

/-- The sum of all `n`-th roots of unity in `ℂ` is `0`, for `1 < n`. -/

lemma sum_nthRootsFinset_eq_zero {n : ℕ} (hn : 1 < n) :
    ∑ ζ ∈ nthRootsFinset n (1 : ℂ), ζ = 0 := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ n :=
    ⟨_, Complex.isPrimitiveRoot_exp n (by omega)⟩
  have hinj : Set.InjOn (fun i : ℕ => ζ ^ i) (Finset.range n) := by
    intro i hi j hj h
    exact hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) h
  have himg : Finset.image (fun i : ℕ => ζ ^ i) (Finset.range n) = nthRootsFinset n (1 : ℂ) := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [Polynomial.mem_nthRootsFinset (by omega), ← pow_mul, mul_comm, pow_mul,
        hζ.pow_eq_one, one_pow]
    · rw [hζ.card_nthRootsFinset, Finset.card_image_of_injOn hinj, Finset.card_range]
  rw [← himg, Finset.sum_image (fun i hi j hj h => hinj hi hj h)]
  exact hζ.geom_sum_eq_zero hn

/-- The sum over the divisors of `n` of the sums of the primitive `d`-th roots of unity
equals the sum of all `n`-th roots of unity. -/
