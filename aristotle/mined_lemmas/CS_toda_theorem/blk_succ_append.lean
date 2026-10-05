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

lemma blk_succ_append {u w : Str} {B j : ℕ} (hu : u.length = B) :
    blk B (j + 1) (u ++ w) = blk B j w := by
  unfold blk
  have h1 : (j + 1) * B = u.length + j * B := by rw [hu]; ring
  rw [h1, List.drop_append, List.drop_eq_nil_of_le (by omega)]
  simp

