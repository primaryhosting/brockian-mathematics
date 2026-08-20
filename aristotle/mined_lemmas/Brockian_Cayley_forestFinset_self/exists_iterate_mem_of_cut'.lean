import Mathlib

namespace Brockian.Cayley

open Finset

/-!
# Cayley's formula

The number of labeled trees on `n` vertices is `n ^ (n - 2)`.

The proof goes through *rooted forests*, encoded as "parent functions": a rooted forest on a
vertex set `A` with set of roots `S ⊆ A` is a function `f : V → V` which fixes everything
outside `A \ S`, maps `A \ S` into `A`, and such that iterating `f` from any vertex of `A`
eventually lands in `S`.

The main counting statement is
`|A| * #(forests on A with roots S) = |S| * |A| ^ (|A| - |S|)`,
proved by induction on `|A|` (deleting a root and summing over the set of its children).

Specialising to `A = univ` and `S = {0}` in `Fin n` and putting rooted forests with a single
root in bijection with trees gives Cayley's formula.
-/

/-! ### Rooted forests, encoded by parent functions -/

section Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `IsForest A S f` says that `f` is the parent function of a rooted forest on the vertex
set `A` whose set of roots is `S`. -/
structure IsForest (A S : Finset V) (f : V → V) : Prop where
  /-- Vertices which are not non-root vertices of the forest are fixed. -/
  fixed : ∀ v, v ∉ A \ S → f v = v
  /-- The parent of a non-root vertex is a vertex. -/
  maps : ∀ v ∈ A \ S, f v ∈ A
  /-- Iterating the parent function eventually reaches a root. -/
  reaches : ∀ v ∈ A, ∃ m, f^[m] v ∈ S

/-- The finset of rooted forests on `A` with roots `S`, encoded by parent functions. -/

lemma exists_iterate_mem_of_cut' {f g : V → V} {C S S' : Finset V} {r : V}
    (hagree : ∀ v, v ∉ C → g v = f v) (hCS' : C ⊆ S') (hSr : ∀ w ∈ S, w ≠ r → w ∈ S')
    (hne : ∀ v, v ≠ r → v ∉ S → v ∉ C → f v ≠ r) :
    ∀ (m : ℕ) (v : V), v ≠ r → f^[m] v ∈ S → ∃ m', g^[m'] v ∈ S' := by
  intro m v hv hfm
  -- Key fact: if all iterates up to n are outside C, then g^[n] v = f^[n] v
  have iter_eq : ∀ n w, (∀ j < n, f^[j] w ∉ C) → g^[n] w = f^[n] w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro w h
      simp only [Function.iterate_succ_apply']
      rw [ih _ fun j hj => h j (Nat.lt_succ_of_lt hj)]
      apply hagree
      exact h n (Nat.lt_succ_self n)
  -- Use classical choice to find the minimum k where f^[k] v ∈ S ∪ C
  have hex : ∃ k, k ≤ m ∧ f^[k] v ∈ S ∪ C := ⟨m, le_refl m, Finset.mem_union_left _ hfm⟩
  let k := Nat.find hex
  have hkP : k ≤ m ∧ f^[k] v ∈ S ∪ C := Nat.find_spec hex
  have hk_le : k ≤ m := hkP.1
  have hksC : f^[k] v ∈ S ∪ C := hkP.2
  -- All previous iterates are outside S ∪ C
  have hbefore : ∀ j < k, f^[j] v ∉ S ∪ C := fun j hj hmem => Nat.find_min hex hj ⟨by omega, hmem⟩
  use k
  -- Since j < k implies f^[j] v ∉ C, we have g^[k] v = f^[k] v
  rw [iter_eq k v fun j hj => by
    intro hfjc
    exact hbefore j hj (by simp [Finset.mem_union]; right; exact hfjc)]
  -- Now g^[k] v = f^[k] v ∈ S ∪ C
  have hksC' := Finset.mem_union.mp hksC
  rcases hksC' with hktS | hktC
  · -- f^[k] v ∈ S
    by_cases hktr : f^[k] v = r
    · -- f^[k] v = r, contradiction with minimality of k
      -- Use strong induction to show this leads to v = r
      exfalso
      have : v = r := by
        have hall : ∀ n ≤ k, f^[n] v = r → v = r := by
          intro n hn hnr
          induction n using Nat.strong_induction_on with
          | _ m ih =>
            by_cases hm0 : m = 0
            · simp [hm0] at hnr
              exact hnr
            · have hm_pos : m > 0 := Nat.pos_of_ne_zero hm0
              have hfnm1 : f (f^[m-1] v) = r := by
                have heq : f^[m] v = f (f^[m-1] v) := by
                  conv_lhs => rw [show m = Nat.succ (m - 1) by omega]
                  exact Function.iterate_succ_apply' f (m - 1) v
                rw [← heq]; exact hnr
              have := hne (f^[m-1] v)
              by_cases hfm1 : f^[m-1] v = r
              · exact ih (m - 1) (by omega) (by omega) hfm1
              · have hfm1_not_S : f^[m-1] v ∉ S := fun h => hbefore (m - 1) (by omega) (Finset.mem_union_left _ h)
                have hfm1_not_C : f^[m-1] v ∉ C := fun h => hbefore (m - 1) (by omega) (Finset.mem_union_right _ h)
                exact absurd hfnm1 (this hfm1 hfm1_not_S hfm1_not_C)
        exact hall k (le_refl k) hktr
      exact hv this
    · exact hSr _ hktS hktr
  · -- f^[k] v ∈ C ⊆ S'
    exact hCS' hktC

/-! #### Cutting the edges into a root -/

/-- Cut the edges going into the root `r`: the children `C` of `r` become roots. -/
