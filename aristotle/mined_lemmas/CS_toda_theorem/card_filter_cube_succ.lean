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

lemma card_filter_cube_succ (n : ℕ) (P : Str → Prop) [DecidablePred P] :
    ((Cube (n + 1)).filter P).card
      = ((Cube n).filter (fun l => P (false :: l))).card
        + ((Cube n).filter (fun l => P (true :: l))).card := by
  have h1 : Cube 1 = {[false], [true]} := by
    ext l
    simp only [mem_cube, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      match l, h with
      | [b], _ => cases b <;> simp
    · rintro (rfl | rfl) <;> simp
  have hn : n + 1 = 1 + n := by omega
  simp only [Finset.card_filter]
  rw [hn, sum_cube_append 1 n]
  rw [h1]
  rw [Finset.sum_insert (by simp)]
  simp

