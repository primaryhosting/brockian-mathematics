import RequestProject.TodaCube

/-!
# Affine hashing over GF(2) and the isolation lemma

We encode an affine hash function `y ↦ A y + b` from `GF(2)^q` to `GF(2)^k` as a bit string
consisting of `q+4` blocks of length `q+1`; block `i` consists of the `i`-th row of `A`
followed by the `i`-th coordinate of `b`.  Only the first `k` blocks are used.

The main results are the two counting lemmas (uniformity and pairwise independence) and the
Valiant–Vazirani isolation lemma `CS.isolation`.
-/

open Classical BigOperators

namespace CS

/-- Inner product over `GF(2)` of two bit strings. -/

theorem prod_sum_blocks {M : Type} [CommSemiring M] (B : ℕ) :
    ∀ (T : ℕ) (g : ℕ → Str → M),
    ∑ v ∈ Cube (T * B), ∏ j ∈ Finset.range T, g j (blk B j v)
      = ∏ j ∈ Finset.range T, ∑ u ∈ Cube B, g j u := by
  intro T
  induction T with
  | zero => intro g; simp [cube_zero]
  | succ T ih =>
      intro g
      have h : (T + 1) * B = B + T * B := by ring
      calc ∑ v ∈ Cube ((T + 1) * B), ∏ j ∈ Finset.range (T + 1), g j (blk B j v)
          = ∑ u ∈ Cube B, ∑ w ∈ Cube (T * B),
              ∏ j ∈ Finset.range (T + 1), g j (blk B j (u ++ w)) := by
            rw [h, sum_cube_append]
        _ = ∑ u ∈ Cube B, ∑ w ∈ Cube (T * B),
              (g 0 u * ∏ j ∈ Finset.range T, g (j + 1) (blk B j w)) := by
            refine Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun w _ => ?_))
            rw [mem_cube] at hu
            rw [Finset.prod_range_succ', blk_zero_append hu, mul_comm]
            congr 1
            exact Finset.prod_congr rfl (fun j _ => by rw [blk_succ_append hu])
        _ = (∑ u ∈ Cube B, g 0 u) *
              (∑ w ∈ Cube (T * B), ∏ j ∈ Finset.range T, g (j + 1) (blk B j w)) := by
            rw [Finset.sum_mul_sum]
        _ = (∑ u ∈ Cube B, g 0 u) * ∏ j ∈ Finset.range T, ∑ u ∈ Cube B, g (j + 1) u := by
            rw [ih (fun j => g (j + 1))]
        _ = ∏ j ∈ Finset.range (T + 1), ∑ u ∈ Cube B, g j u := by
            rw [Finset.prod_range_succ']; ring

/-- Counting version of `prod_sum_blocks`. -/
