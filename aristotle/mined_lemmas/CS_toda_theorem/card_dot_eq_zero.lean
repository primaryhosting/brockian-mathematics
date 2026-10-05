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

lemma card_dot_eq_zero : ∀ (d : Str), true ∈ d →
    ((Cube d.length).filter (fun a => dot a d = false)).card * 2 = 2 ^ d.length := by
  intro d
  induction d with
  | nil => intro h; simp at h
  | cons b d ih =>
      intro hmem
      rw [List.length_cons, card_filter_cube_succ]
      cases b with
      | true =>
          have h1 : ((Cube d.length).filter (fun l => dot (false :: l) (true :: d) = false)).card
              = ((Cube d.length).filter (fun l => dot l d = false)).card := by
            congr 1
            apply Finset.filter_congr
            intro l _
            simp
          have h2 : ((Cube d.length).filter (fun l => dot (true :: l) (true :: d) = false)).card
              = ((Cube d.length).filter (fun l => ¬ (dot l d = false))).card := by
            congr 1
            apply Finset.filter_congr
            intro l _
            simp
          rw [h1, h2, Finset.card_filter_add_card_filter_not, card_cube]
          ring
      | false =>
          have hmem' : true ∈ d := by simpa using hmem
          have h1 : ∀ (c : Bool), ((Cube d.length).filter
              (fun l => dot (c :: l) (false :: d) = false)).card
              = ((Cube d.length).filter (fun l => dot l d = false)).card := by
            intro c
            congr 1
            apply Finset.filter_congr
            intro l _
            simp
          rw [h1 false, h1 true]
          have := ih hmem'
          rw [pow_succ]
          omega

/-! ### Linearity of `dot` -/

