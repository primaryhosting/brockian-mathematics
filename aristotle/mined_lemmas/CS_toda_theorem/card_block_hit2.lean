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

lemma card_block_hit2 (q : ℕ) (y y' : Str) (hy : y.length = q) (hy' : y'.length = q)
    (hne : y ≠ y') :
    ((Cube (q + 1)).filter
      (fun u => dot (u.take q) y = u.getD q false ∧
        dot (u.take q) y' = u.getD q false)).card * 2 = 2 ^ q := by
  simp only [Finset.card_filter]
  rw [sum_cube_append q 1]
  have h1 : Cube 1 = {[false], [true]} := by
    ext l
    simp only [mem_cube, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      match l, h with
      | [b], _ => cases b <;> simp
    · rintro (rfl | rfl) <;> simp
  rw [h1]
  have key : ∀ a ∈ Cube q, (∑ w ∈ ({[false], [true]} : Finset Str),
      if (dot ((a ++ w).take q) y = (a ++ w).getD q false ∧
          dot ((a ++ w).take q) y' = (a ++ w).getD q false) then (1 : ℕ) else 0)
      = (if dot a (List.zipWith xor y y') = false then 1 else 0) := by
    intro a ha
    rw [mem_cube] at ha
    rw [Finset.sum_insert (by simp)]
    have e1 : ∀ (c : Bool), ((a ++ [c]).take q) = a := by
      intro c; rw [← ha]; simp
    have e2 : ∀ (c : Bool), ((a ++ [c]).getD q false) = c := by
      intro c
      rw [← ha]
      simp [List.getD_eq_getElem?_getD]
    simp only [Finset.sum_singleton, e1, e2]
    rw [dot_xor a y y' (by rw [hy, hy'])]
    cases h : dot a y <;> cases h' : dot a y' <;> simp
  rw [Finset.sum_congr rfl key]
  have hlen : (List.zipWith xor y y').length = q := by
    rw [zipWith_xor_length y y' (by rw [hy, hy']), hy]
  have hmem : true ∈ List.zipWith xor y y' := zipWith_xor_mem y y' (by rw [hy, hy']) hne
  have := card_dot_eq_zero (List.zipWith xor y y') hmem
  rw [hlen] at this
  rw [← Finset.card_filter]
  exact this

/-- The general block-counting lemma for hash functions. -/
