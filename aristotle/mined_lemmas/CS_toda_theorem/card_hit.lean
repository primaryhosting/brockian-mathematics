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

theorem card_hit (q k : ℕ) (hk : k ≤ q + 4) (y : Str) (hy : y.length = q) :
    ((Cube (hashLen q)).filter (fun h => Hit q k h y)).card * 2 ^ k = 2 ^ hashLen q := by
  have := card_hash_blocks q k 1 hk (fun u => dot (u.take q) y = u.getD q false)
    (by rw [card_block_hit q y hy]; ring)
  simpa [Hit] using this

/-- Pairwise independence: for distinct `y ≠ y'` the fraction of hash functions hitting both
is `4^{-k}`. -/
