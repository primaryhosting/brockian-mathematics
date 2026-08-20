import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem children_approx {n : ℕ} (β : ℕ → Bool) (t : ℕ) (ht : 1 ≤ t) (hq2 : 2 ≤ q)
    (cs : List Circuit)
    (ih : ∀ c ∈ cs, ∃ P ∈ Deg F n ((t * (q - 1)) ^ c.depth),
      2 ^ t * #(errSet P (fun x => c.eval q (ext β x))) ≤ c.size * 2 ^ n) :
    ∃ (g : Fin cs.length → (Cube n → F)) (B : Finset (Cube n)),
      (∀ i, g i ∈ Deg F n ((t * (q - 1)) ^ ((cs.map Circuit.depth).foldr max 0))) ∧
      (∀ x, x ∉ B → ∀ i, g i x = bitv F ((cs.get i).eval q (ext β x))) ∧
      2 ^ t * #B ≤ (cs.map Circuit.size).sum * 2 ^ n := by
  classical
  have hbase : 1 ≤ t * (q - 1) := by
    have := Nat.mul_le_mul ht (show 1 ≤ q - 1 by omega)
    simpa using this
  choose! Pf hPf1 hPf2 using ih
  refine ⟨fun i => Pf (cs.get i), univ.biUnion (fun i : Fin cs.length =>
    errSet (Pf (cs.get i)) (fun x => (cs.get i).eval q (ext β x))), ?_, ?_, ?_⟩
  · intro i
    refine mem_Deg_of_le (hPf1 _ (List.get_mem cs i)) ?_
    exact Nat.pow_le_pow_right hbase (Circuit.depth_le_of_mem (List.get_mem cs i))
  · intro x hx i
    by_contra hc
    exact hx (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, mem_errSet.2 hc⟩)
  · calc 2 ^ t * #(univ.biUnion (fun i : Fin cs.length =>
            errSet (Pf (cs.get i)) (fun x => (cs.get i).eval q (ext β x))))
        ≤ 2 ^ t * ∑ i : Fin cs.length,
            #(errSet (Pf (cs.get i)) (fun x => (cs.get i).eval q (ext β x))) :=
          Nat.mul_le_mul_left _ (Finset.card_biUnion_le)
      _ = ∑ i : Fin cs.length,
            2 ^ t * #(errSet (Pf (cs.get i)) (fun x => (cs.get i).eval q (ext β x))) :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ i : Fin cs.length, (cs.get i).size * 2 ^ n :=
          Finset.sum_le_sum fun i _ => hPf2 _ (List.get_mem cs i)
      _ = (cs.map Circuit.size).sum * 2 ^ n := by
          rw [← Finset.sum_mul, ← list_sum_map]

/-- **Razborov–Smolensky approximation lemma.** -/
