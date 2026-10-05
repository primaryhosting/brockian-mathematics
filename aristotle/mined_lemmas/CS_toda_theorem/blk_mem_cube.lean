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

lemma blk_mem_cube {B j T : ℕ} {v : Str} (hv : v ∈ Cube (T * B)) (hj : j < T) :
    blk B j v ∈ Cube B := by
  rw [mem_cube] at hv ⊢
  simp only [blk, List.length_take, List.length_drop, hv]
  have h2 : j * B + B ≤ T * B := by
    calc j * B + B = (j + 1) * B := by ring
      _ ≤ T * B := Nat.mul_le_mul_right _ hj
  omega

/-- Factorisation of a sum of block-wise products over a cube. -/
