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

lemma card_hash_blocks (q k d : ℕ) (hk : k ≤ q + 4) (Q : Str → Prop) [DecidablePred Q]
    (hQ : ((Cube (q + 1)).filter Q).card * d = 2 ^ q) :
    ((Cube (hashLen q)).filter (fun h => ∀ i < k, Q (blk (q + 1) i h))).card * (d ^ k * 2 ^ k)
      = 2 ^ hashLen q := by
  set A := ((Cube (q + 1)).filter Q).card with hA
  have hfilter : ((Cube ((q + 4) * (q + 1))).filter
      (fun h => ∀ i < (q + 4), (i < k → Q (blk (q + 1) i h)))).card
      = ∏ i ∈ Finset.range (q + 4), ((Cube (q + 1)).filter (fun u => i < k → Q u)).card := by
    convert card_filter_blocks (q + 4) (q + 1) (fun i u => i < k → Q u) using 2
  have hset : ((Cube (hashLen q)).filter (fun h => ∀ i < k, Q (blk (q + 1) i h))).card
      = ((Cube ((q + 4) * (q + 1))).filter
          (fun h => ∀ i < (q + 4), (i < k → Q (blk (q + 1) i h)))).card := by
    congr 1
    ext h
    simp only [Finset.mem_filter, mem_cube, hashLen]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun i _ hik => h2 i hik⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun i hik => h2 i (lt_of_lt_of_le hik hk) hik⟩
  have hcount : ∀ i ∈ Finset.range (q + 4),
      ((Cube (q + 1)).filter (fun u => i < k → Q u)).card = if i < k then A else 2 ^ (q + 1) := by
    intro i _
    by_cases hik : i < k
    · rw [if_pos hik, hA]
      congr 1
      ext u
      simp [hik]
    · rw [if_neg hik, ← card_cube (q + 1)]
      congr 1
      ext u
      simp [hik]
  have e1 : ∏ i ∈ Finset.Ico 0 k, (if i < k then A else 2 ^ (q + 1)) = A ^ k := by
    rw [Finset.prod_congr rfl (fun i hi => by
      simp only [Finset.mem_Ico] at hi; rw [if_pos hi.2])]
    simp
  have e2 : ∏ i ∈ Finset.Ico k (q + 4), (if i < k then A else 2 ^ (q + 1))
      = (2 ^ (q + 1)) ^ (q + 4 - k) := by
    rw [Finset.prod_congr rfl (fun i hi => by
      simp only [Finset.mem_Ico] at hi; rw [if_neg (Nat.not_lt.2 hi.1)])]
    simp
  rw [hset, hfilter, Finset.prod_congr rfl hcount, Finset.range_eq_Ico,
    ← Finset.prod_Ico_consecutive _ (Nat.zero_le k) hk, e1, e2]
  calc A ^ k * (2 ^ (q + 1)) ^ (q + 4 - k) * (d ^ k * 2 ^ k)
      = (A * d) ^ k * 2 ^ k * (2 ^ (q + 1)) ^ (q + 4 - k) := by rw [mul_pow]; ring
    _ = 2 ^ ((q + 1) * k) * (2 ^ (q + 1)) ^ (q + 4 - k) := by
        rw [hQ, ← pow_mul, ← pow_mul, ← pow_add]
        congr 1
        ring
    _ = 2 ^ hashLen q := by
        rw [← pow_mul, ← pow_add, hashLen]
        congr 1
        obtain ⟨c, hc⟩ := Nat.le.dest hk
        have h4 : q + 4 - k = c := by omega
        rw [h4, ← hc]
        ring

/-- Uniformity: for a fixed `y`, the fraction of hash functions hitting `y` is `2^{-k}`. -/
