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

theorem sum_cube_append {M : Type} [AddCommMonoid M] (a b : ℕ) (F : Str → M) :
    ∑ v ∈ Cube (a + b), F v = ∑ u ∈ Cube a, ∑ w ∈ Cube b, F (u ++ w) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (i := fun v => (v.take a, v.drop a)) (j := fun p => p.1 ++ p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro v hv; rw [mem_cube] at hv; simp [Finset.mem_product, mem_cube, hv]
  · rintro ⟨u, w⟩ h; simp [Finset.mem_product, mem_cube] at h; simp [mem_cube, h.1, h.2]
  · intro v hv; simp
  · rintro ⟨u, w⟩ h; simp [Finset.mem_product, mem_cube] at h; simp [h.1]
  · intro v hv; simp

/-- The `j`-th block of length `B` of a string. -/
