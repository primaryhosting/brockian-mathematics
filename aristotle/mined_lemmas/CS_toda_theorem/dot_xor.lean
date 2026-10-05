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

lemma dot_xor : ∀ (a y y' : Str), y.length = y'.length →
    dot a (List.zipWith xor y y') = xor (dot a y) (dot a y') := by
  intro a
  induction a with
  | nil => intro y y' _; simp
  | cons c a ih =>
      intro y y' hlen
      match y, y' with
      | [], [] => simp
      | (b :: y), (b' :: y') =>
          simp only [List.zipWith_cons_cons, dot_cons]
          rw [ih y y' (by simpa using hlen)]
          cases c <;> cases b <;> cases b' <;> simp [Bool.xor_assoc, Bool.xor_comm,
            Bool.xor_left_comm]

