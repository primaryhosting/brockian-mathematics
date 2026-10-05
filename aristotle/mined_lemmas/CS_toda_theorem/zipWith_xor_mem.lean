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

lemma zipWith_xor_mem : ∀ (y y' : Str), y.length = y'.length → y ≠ y' →
    true ∈ List.zipWith xor y y' := by
  intro y
  induction y with
  | nil => intro y' hlen hne; cases y' <;> simp_all
  | cons b y ih =>
      intro y' hlen hne
      match y' with
      | (b' :: y') =>
          by_cases hb : b = b'
          · subst hb
            have hne' : y ≠ y' := by
              intro h; exact hne (by rw [h])
            have := ih y' (by simpa using hlen) hne'
            simp [this]
          · have : xor b b' = true := by cases b <;> cases b' <;> simp_all
            simp [this]

