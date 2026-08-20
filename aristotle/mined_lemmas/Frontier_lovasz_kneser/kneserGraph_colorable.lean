/-
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is
-- repeated as the module docstring immediately after the import.)

import Mathlib

/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset SimpleGraph

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of an `n`-element set,
two of them being adjacent when they are disjoint.  (For `k ≥ 1` disjointness already forces
the two vertices to be distinct; the explicit `s ≠ t` only serves to make the relation
irreflexive in the degenerate case `k = 0`.) -/

theorem kneserGraph_colorable (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (kneserGraph n k).Colorable (n - 2 * k + 2) := by
  set m : ℕ := n - 2 * k + 1 with hm
  have hmn : m < n := by omega
  have hne : ∀ s : KneserVertex n k, ((s : Finset (Fin n)).image Fin.val).Nonempty := by
    intro s
    have h : (s : Finset (Fin n)).Nonempty := Finset.card_pos.1 (by rw [s.2]; omega)
    exact h.image _
  set c : KneserVertex n k → ℕ :=
    fun s => min (((s : Finset (Fin n)).image Fin.val).min' (hne s)) m with hc
  have hbound : ∀ s : KneserVertex n k, c s < n - 2 * k + 2 := by
    intro s
    have h := min_le_right (((s : Finset (Fin n)).image Fin.val).min' (hne s)) m
    simp only [hc]
    omega
  have hmem : ∀ s : KneserVertex n k, ∃ i ∈ (s : Finset (Fin n)),
      (i : ℕ) = ((s : Finset (Fin n)).image Fin.val).min' (hne s) := by
    intro s
    have h := Finset.min'_mem _ (hne s)
    rcases Finset.mem_image.1 h with ⟨i, hi, hi'⟩
    exact ⟨i, hi, hi'⟩
  have hle : ∀ (s : KneserVertex n k), ∀ i ∈ (s : Finset (Fin n)),
      ((s : Finset (Fin n)).image Fin.val).min' (hne s) ≤ (i : ℕ) := by
    intro s i hi
    exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hi)
  refine ⟨SimpleGraph.Coloring.mk (fun s => (⟨c s, hbound s⟩ : Fin (n - 2 * k + 2))) ?_⟩
  rintro s t ⟨hst, hd⟩ heq
  have hcst : c s = c t := congrArg Fin.val heq
  have hcs : c s = min (((s : Finset (Fin n)).image Fin.val).min' (hne s)) m := rfl
  have hct : c t = min (((t : Finset (Fin n)).image Fin.val).min' (hne t)) m := rfl
  set A := ((s : Finset (Fin n)).image Fin.val).min' (hne s) with hA
  set B := ((t : Finset (Fin n)).image Fin.val).min' (hne t) with hB
  rcases lt_or_ge A m with hAm | hAm
  · -- the two minima agree and are `< m`, so the sets share their minimal element
    have hBA : B = A := by omega
    obtain ⟨i, hi, hival⟩ := hmem s
    obtain ⟨j, hj, hjval⟩ := hmem t
    have hij : i = j := by
      apply Fin.ext
      rw [hival, hjval, ← hA, ← hB, hBA]
    subst hij
    exact (Finset.disjoint_left.1 hd hi) hj
  · -- both sets live inside the last `2k - 1` elements, which is too small
    have hBm : m ≤ B := by omega
    have hsub : (s : Finset (Fin n)) ∪ (t : Finset (Fin n)) ⊆ Finset.Ici (⟨m, hmn⟩ : Fin n) := by
      intro i hi
      rcases Finset.mem_union.1 hi with h | h
      · have h2 := hle s i h
        simp only [Finset.mem_Ici, Fin.le_def]
        omega
      · have h2 := hle t i h
        simp only [Finset.mem_Ici, Fin.le_def]
        omega
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd, s.2, t.2, Fin.card_Ici] at hcard
    simp only at hcard
    omega

/-- The chromatic number of the Kneser graph is at most `n - 2k + 2`. -/
