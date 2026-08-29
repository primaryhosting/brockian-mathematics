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

private lemma isolation_arith {Om K s X SN SN2 : ℕ}
    (m1 : SN * K = s * Om) (m2 : SN2 * (K * K) + s * Om = s * Om * K + s * s * Om)
    (pt : 2 * SN ≤ X + SN2) (hsk : 4 * s ≤ K) (hks : K ≤ 8 * s) (hs1 : 1 ≤ s)
    (hKpos : 0 < K) : Om ≤ 16 * X := by
  have h5 : 2 * SN * (K * K) ≤ (X + SN2) * (K * K) := Nat.mul_le_mul_right _ pt
  have h6 : 2 * SN * (K * K) = 2 * (s * Om) * K := by
    calc 2 * SN * (K * K) = 2 * (SN * K) * K := by ring
      _ = 2 * (s * Om) * K := by rw [m1]
  have h7 : (X + SN2) * (K * K) + s * Om = X * (K * K) + (s * Om * K + s * s * Om) := by
    rw [add_mul, add_assoc, m2]
  have h9 : 2 * (s * Om) * K + s * Om ≤ X * (K * K) + (s * Om * K + s * s * Om) := by
    rw [← h7, ← h6]
    exact Nat.add_le_add_right h5 _
  have h8 : s * Om * K + s * Om ≤ X * (K * K) + s * s * Om := by nlinarith [h9]
  have a1 : K * K ≤ 8 * s * K := Nat.mul_le_mul_right K hks
  have a2 : 4 * s * (4 * s) ≤ 4 * s * K := Nat.mul_le_mul_left (4 * s) hsk
  have hquad : K * K + 16 * (s * s) ≤ 16 * (s * K) + 16 * s := by nlinarith [a1, a2]
  have hq2 : (K * K + 16 * (s * s)) * Om ≤ (16 * (s * K) + 16 * s) * Om :=
    Nat.mul_le_mul_right Om hquad
  have h8' : 16 * (s * Om * K + s * Om) ≤ 16 * (X * (K * K) + s * s * Om) :=
    Nat.mul_le_mul_left 16 h8
  have hfin : Om * (K * K) ≤ 16 * X * (K * K) := by nlinarith [hq2, h8']
  exact Nat.le_of_mul_le_mul_right hfin (by positivity)

/-- **Valiant–Vazirani isolation lemma**.  If `S` is a nonempty set of `q`-bit strings and
`2^k` is within a factor of two of `4 |S|`, then for at least a `1/16` fraction of the hash
functions, `S` contains exactly one point hit by the hash, hence an odd number of them. -/
