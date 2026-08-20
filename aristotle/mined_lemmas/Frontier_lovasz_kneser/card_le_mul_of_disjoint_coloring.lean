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

theorem card_le_mul_of_disjoint_coloring {n k c : ℕ} (hk : 1 ≤ k) (h2k : 2 * k ≤ n)
    (f : Finset (Fin n) → ℕ) (hfc : ∀ A : Finset (Fin n), A.card = k → f A < c)
    (hf : ∀ A B : Finset (Fin n), A.card = k → B.card = k → Disjoint A B → f A ≠ f B) :
    n ≤ c * k := by
  classical
  set P := Finset.powersetCard k (Finset.univ : Finset (Fin n)) with hP
  have hmemP : ∀ A ∈ P, A.card = k := by
    intro A hA
    exact (Finset.mem_powersetCard.mp hA).2
  have hPcard : P.card = n.choose k := by
    rw [hP, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hfib : P.card = ∑ i ∈ Finset.range c, (P.filter (fun A => f A = i)).card :=
    Finset.card_eq_sum_card_fiberwise (fun A hA => Finset.mem_range.mpr (hfc A (hmemP A hA)))
  have hEKR : ∀ i ∈ Finset.range c,
      (P.filter (fun A => f A = i)).card ≤ (n - 1).choose (k - 1) := by
    intro i _
    refine Finset.erdos_ko_rado ?_ ?_ (by omega)
    · intro A hA B hB hd
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hA hB
      exact hf A B (hmemP A hA.1) (hmemP B hB.1) hd (hA.2.trans hB.2.symm)
    · intro A hA
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hA
      exact hmemP A hA.1
  have hsum : n.choose k ≤ c * (n - 1).choose (k - 1) := by
    calc n.choose k = ∑ i ∈ Finset.range c, (P.filter (fun A => f A = i)).card := by
          rw [← hfib, hPcard]
      _ ≤ ∑ _i ∈ Finset.range c, (n - 1).choose (k - 1) := Finset.sum_le_sum hEKR
      _ = c * (n - 1).choose (k - 1) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hid : n * (n - 1).choose (k - 1) = n.choose k * k := by
    have h := Nat.add_one_mul_choose_eq (n - 1) (k - 1)
    rwa [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)] at h
  have hpos : 0 < (n - 1).choose (k - 1) := Nat.choose_pos (by omega)
  have hfinal : n * (n - 1).choose (k - 1) ≤ (c * k) * (n - 1).choose (k - 1) := by
    calc n * (n - 1).choose (k - 1) = n.choose k * k := hid
      _ ≤ (c * (n - 1).choose (k - 1)) * k := Nat.mul_le_mul_right k hsum
      _ = (c * k) * (n - 1).choose (k - 1) := by ring
  exact Nat.le_of_mul_le_mul_right hfinal hpos

