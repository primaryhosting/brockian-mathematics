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

theorem card_hit2 (q k : ℕ) (hk : k ≤ q + 4) (y y' : Str) (hy : y.length = q)
    (hy' : y'.length = q) (hne : y ≠ y') :
    ((Cube (hashLen q)).filter (fun h => Hit q k h y ∧ Hit q k h y')).card * 2 ^ (2 * k)
      = 2 ^ hashLen q := by
  have hb := card_block_hit2 q y y' hy hy' hne
  have := card_hash_blocks q k 2 hk
    (fun u => dot (u.take q) y = u.getD q false ∧ dot (u.take q) y' = u.getD q false) hb
  have hpow : (2 : ℕ) ^ k * 2 ^ k = 2 ^ (2 * k) := by
    rw [← pow_add]; congr 1; ring
  rw [hpow] at this
  rw [← this]
  congr 2
  ext h
  simp only [Finset.mem_filter, Hit]
  constructor
  · rintro ⟨hm, h1, h2⟩; exact ⟨hm, fun i hi => ⟨h1 i hi, h2 i hi⟩⟩
  · rintro ⟨hm, h1⟩; exact ⟨hm, fun i hi => (h1 i hi).1, fun i hi => (h1 i hi).2⟩

/-! ### The isolation lemma -/

/-- **Valiant–Vazirani isolation lemma**.  If `S` is a nonempty set of `q`-bit strings and
`2^k` is within a factor of two of `4 |S|`, then for at least a `1/16` fraction of the hash
functions, `S` contains exactly one point hit by the hash, hence an odd number of them. -/
