import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# The Kneser graph and Lovász' theorem

The Kneser graph `KG_{n,k}` has as vertices the `k`-element subsets of an `n`-element set,
two of them being adjacent when they are disjoint.  Lovász' theorem (Kneser's conjecture)
states that its chromatic number equals `n - 2k + 2` for `n ≥ 2k`.

The upper bound `χ(KG_{n,k}) ≤ n - 2k + 2` is elementary and is proved here in full
generality (`Frontier.kneserGraph_colorable`).

The matching lower bound is the hard half; the known proofs go through the Borsuk–Ulam
theorem (or its combinatorial cousin, Tucker's lemma), neither of which is available in
Mathlib.  Here we prove the lower bound in the base cases that are accessible by the
Erdős–Ko–Rado theorem, namely `k = 1` (where `KG_{n,1}` is the complete graph `K_n`),
`n = 2k` (a perfect matching) and `n = 2k+1` (the odd graphs, e.g. the Petersen graph
`KG_{5,2}`).  This is the content of `Frontier.lovasz_kneser`.
-/

namespace Frontier

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of `Fin n`, and two
distinct such subsets are adjacent when they are disjoint. -/

lemma kneserColor_ne_of_disjoint {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    {A B : Finset (Fin n)} (hA : A.card = k) (hB : B.card = k) (hAB : Disjoint A B) :
    kneserColor n k A ≠ kneserColor n k B := by
  have hA' : A.Nonempty := Finset.card_pos.mp (by omega)
  have hB' : B.Nonempty := Finset.card_pos.mp (by omega)
  intro hcol
  unfold kneserColor at hcol
  rw [dif_pos hA', dif_pos hB'] at hcol
  by_cases hab : (A.min' hA').val < n - 2 * k + 1 ∧ (B.min' hB').val < n - 2 * k + 1
  · have hval : (A.min' hA').val = (B.min' hB').val := by omega
    have hmemA : A.min' hA' ∈ A := Finset.min'_mem _ _
    have hmemB : B.min' hB' ∈ B := Finset.min'_mem _ _
    have heq : A.min' hA' = B.min' hB' := Fin.ext hval
    exact (Finset.disjoint_left.mp hAB hmemA) (heq ▸ hmemB)
  · have hge : n - 2 * k + 1 ≤ (A.min' hA').val ∧ n - 2 * k + 1 ≤ (B.min' hB').val := by omega
    have hcard : (A ∪ B).card = 2 * k := by
      rw [Finset.card_union_of_disjoint hAB, hA, hB]; ring
    have hsub : ∀ x ∈ A ∪ B, (x.val) ∈ Finset.Ico (n - 2 * k + 1) n := by
      intro x hx
      simp only [Finset.mem_Ico]
      refine ⟨?_, x.isLt⟩
      rcases Finset.mem_union.mp hx with h | h
      · exact le_trans hge.1 (Finset.min'_le A x h)
      · exact le_trans hge.2 (Finset.min'_le B x h)
    have hle := Finset.card_le_card_of_injOn (s := A ∪ B)
      (t := Finset.Ico (n - 2 * k + 1) n) (fun x : Fin n => x.val) hsub
      (fun x _ y _ h => Fin.ext h)
    rw [hcard, Nat.card_Ico] at hle
    omega

