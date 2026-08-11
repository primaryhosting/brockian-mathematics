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
def kneserGraph (n k : ℕ) : SimpleGraph (KneserVertex n k) where
  Adj s t := s ≠ t ∧ Disjoint s.1 t.1
  symm := by
    rintro s t ⟨h₁, h₂⟩
    exact ⟨h₁.symm, h₂.symm⟩
  loopless := ⟨fun s h => h.1 rfl⟩

@[simp] lemma kneserGraph_adj {n k : ℕ} (s t : KneserVertex n k) :
    (kneserGraph n k).Adj s t ↔ s ≠ t ∧ Disjoint s.1 t.1 := Iff.rfl

/-! ### The upper bound -/

/-- The explicit colouring of the Kneser graph used for the upper bound: a set is coloured by
its smallest element, all elements `≥ n - 2k + 1` being identified. -/
noncomputable def kneserColor (n k : ℕ) (A : Finset (Fin n)) : ℕ :=
  if h : A.Nonempty then min ((A.min' h).val) (n - 2 * k + 1) else 0

lemma kneserColor_lt {n k : ℕ} (A : Finset (Fin n)) :
    kneserColor n k A < n - 2 * k + 2 := by
  unfold kneserColor
  split <;> omega

/-- Two disjoint `k`-sets receive different colours. -/
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

theorem kneserGraph_colorable (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (kneserGraph n k).Colorable (n - 2 * k + 2) := by
  rw [SimpleGraph.colorable_iff_exists_bdd_nat_coloring]
  refine ⟨SimpleGraph.Coloring.mk (fun s => kneserColor n k s.1) ?_,
    fun v => kneserColor_lt _⟩
  rintro s t ⟨-, hd⟩
  exact kneserColor_ne_of_disjoint hk hn s.2 t.2 hd

/-! ### The lower bound via Erdős–Ko–Rado -/

/-- If the `k`-subsets of `Fin n` are coloured with `c` colours so that disjoint sets get
different colours, then `n ≤ c * k`.  This is the Erdős–Ko–Rado bound applied to each
colour class. -/
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

theorem kneser_le_of_colorable {n k c : ℕ} (hk : 1 ≤ k) (h2k : 2 * k ≤ n)
    (hc : (kneserGraph n k).Colorable c) : n ≤ c * k := by
  classical
  rw [SimpleGraph.colorable_iff_exists_bdd_nat_coloring] at hc
  obtain ⟨C, hC⟩ := hc
  refine card_le_mul_of_disjoint_coloring (c := c) hk h2k
    (fun A => if h : A.card = k then C ⟨A, h⟩ else 0) ?_ ?_
  · intro A hA
    dsimp only
    rw [dif_pos hA]
    exact hC _
  · intro A B hA hB hd
    dsimp only
    rw [dif_pos hA, dif_pos hB]
    refine C.valid ⟨?_, hd⟩
    intro hAB
    have hAB' : A = B := congrArg Subtype.val hAB
    subst hAB'
    have hempty : A = ∅ :=
      Finset.eq_empty_of_forall_notMem (fun x hx => Finset.disjoint_left.mp hd hx hx)
    rw [hempty, Finset.card_empty] at hA
    omega

/-! ### The main theorem -/

/-- **Lovász' theorem on Kneser graphs (base cases).**

The chromatic number of the Kneser graph `KG_{n,k}` is `n - 2k + 2`.

The general statement is Kneser's conjecture, proved by Lovász via the Borsuk–Ulam theorem,
which is not available in Mathlib.  We prove here the base cases `k = 1` (the complete graph
`K_n`) and `2k ≤ n ≤ 2k + 1` (perfect matchings and the odd graphs), where the lower bound
follows from the Erdős–Ko–Rado theorem.  The upper bound `≤ n - 2k + 2` holds in general and
is `Frontier.kneserGraph_colorable`. -/
theorem lovasz_kneser (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (hcase : k = 1 ∨ n ≤ 2 * k + 1) :
    (kneserGraph n k).chromaticNumber = (n - 2 * k + 2 : ℕ) := by
  refine le_antisymm (kneserGraph_colorable n k hk hn).chromaticNumber_le ?_
  rw [SimpleGraph.le_chromaticNumber_iff_colorable]
  intro m hm
  have hmk : n ≤ m * k := kneser_le_of_colorable hk hn hm
  rcases hcase with rfl | hcase
  · rw [mul_one] at hmk
    omega
  · by_contra hlt
    push_neg at hlt
    have hm2 : m ≤ 2 := by omega
    have hbound : m * k ≤ 2 * k := Nat.mul_le_mul_right k hm2
    -- so `n ≤ 2 * k`, forcing `n = 2 * k` and hence `m ≤ 1`
    have hn2k : n = 2 * k := by omega
    have hm1 : m ≤ 1 := by omega
    have hbound' : m * k ≤ 1 * k := Nat.mul_le_mul_right k hm1
    rw [one_mul] at hbound'
    omega

/-- The chromatic number of the Petersen graph `KG_{5,2}` is `3`. -/
theorem chromaticNumber_petersen : (kneserGraph 5 2).chromaticNumber = 3 := by
  have := lovasz_kneser 5 2 (by norm_num) (by norm_num) (Or.inr (by norm_num))
  norm_num at this
  exact this

end Frontier

