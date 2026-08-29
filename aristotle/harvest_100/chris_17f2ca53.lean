/-
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The vertices of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of an `n`-element set,
and two of them are adjacent when they are distinct and disjoint.  (For `k ≥ 1` the
distinctness condition is automatic; it is included only so that the relation is
irreflexive also in the degenerate case `k = 0`.) -/
def kneserGraph (n k : ℕ) : SimpleGraph (KneserVertex n k) where
  Adj s t := s ≠ t ∧ Disjoint s.1 t.1
  symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp] lemma kneserGraph_adj {n k : ℕ} (s t : KneserVertex n k) :
    (kneserGraph n k).Adj s t ↔ s ≠ t ∧ Disjoint s.1 t.1 := Iff.rfl

/-- Every vertex of `KG_{n,k}` with `k ≥ 1` is a nonempty finset. -/
lemma kneser_vertex_nonempty {n k : ℕ} (hk : 1 ≤ k) (s : KneserVertex n k) : s.1.Nonempty := by
  rw [← Finset.card_pos, s.2]; omega

/-- **Easy direction of the Lovász–Kneser theorem**: the Kneser graph `KG_{n,k}` is
`(n - 2k + 2)`-colorable.  The coloring assigns to a `k`-set `s` the minimum of its least
element and `n - 2k + 1`. -/
theorem kneser_colorable (n k : ℕ) (hk : 1 ≤ k) (h2k : 2 * k ≤ n) :
    (kneserGraph n k).Colorable (n - 2 * k + 2) := by
  classical
  set m := n - 2 * k + 1 with hm
  have hne : ∀ s : KneserVertex n k, s.1.Nonempty := kneser_vertex_nonempty hk
  refine ⟨SimpleGraph.Coloring.mk
    (fun s => (⟨min ((s.1.min' (hne s)) : Fin n).val m, by omega⟩ : Fin (n - 2 * k + 2))) ?_⟩
  rintro s t ⟨hst, hdisj⟩ heq
  simp only [Fin.mk.injEq] at heq
  set a := ((s.1.min' (hne s)) : Fin n).val with ha'
  set b := ((t.1.min' (hne t)) : Fin n).val with hb'
  by_cases ha : a < m
  · have hab : a = b := by omega
    have h1 : s.1.min' (hne s) ∈ s.1 := Finset.min'_mem _ _
    have h2 : t.1.min' (hne t) ∈ t.1 := Finset.min'_mem _ _
    have hEq : s.1.min' (hne s) = t.1.min' (hne t) := Fin.ext hab
    exact (Finset.disjoint_left.mp hdisj h1) (hEq ▸ h2)
  · have hb : ¬ b < m := by omega
    have hsub : ((s.1 ∪ t.1).image Fin.val) ⊆ Finset.Ico m n := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_union] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [Finset.mem_Ico]
      refine ⟨?_, y.isLt⟩
      rcases hy with hy | hy
      · have h := Finset.min'_le s.1 y hy
        rw [Fin.le_def] at h
        omega
      · have h := Finset.min'_le t.1 y hy
        rw [Fin.le_def] at h
        omega
    have hcard : ((s.1 ∪ t.1).image Fin.val).card = 2 * k := by
      rw [Finset.card_image_of_injective _ Fin.val_injective,
        Finset.card_union_of_disjoint hdisj, s.2, t.2]
      ring
    have hle := Finset.card_le_card hsub
    rw [hcard, Nat.card_Ico] at hle
    omega

/-- For `k = 1` the Kneser graph is the complete graph, so its chromatic number is `n`. -/
theorem kneser_chromaticNumber_of_k_eq_one (n : ℕ) (h2 : 2 ≤ n) :
    (kneserGraph n 1).chromaticNumber = (n - 2 * 1 + 2 : ℕ) := by
  have hupper : (kneserGraph n 1).chromaticNumber ≤ (n - 2 * 1 + 2 : ℕ) :=
    (kneser_colorable n 1 le_rfl (by omega)).chromaticNumber_le
  have hlower : (n : ℕ∞) ≤ (kneserGraph n 1).chromaticNumber := by
    refine SimpleGraph.le_chromaticNumber_of_pairwise_adj (ι := Fin n) (by simp)
      (fun i => ⟨{i}, by simp⟩) ?_
    intro i j hij
    refine ⟨?_, ?_⟩
    · simp only [ne_eq, Subtype.mk.injEq, Finset.singleton_inj]
      exact hij
    · simpa using hij
  have hn : n - 2 * 1 + 2 = n := by omega
  rw [hn] at hupper ⊢
  exact le_antisymm hupper hlower

/-- For `n = 2k` (with `k ≥ 1`) the Kneser graph is a perfect matching, so its chromatic
number is `2`. -/
theorem kneser_chromaticNumber_of_n_eq_two_mul_k (k : ℕ) (hk : 1 ≤ k) :
    (kneserGraph (2 * k) k).chromaticNumber = (2 * k - 2 * k + 2 : ℕ) := by
  classical
  have hupper : (kneserGraph (2 * k) k).chromaticNumber ≤ (2 * k - 2 * k + 2 : ℕ) :=
    (kneser_colorable (2 * k) k hk le_rfl).chromaticNumber_le
  have hkn : k < 2 * k := by omega
  set i : Fin (2 * k) := ⟨k, hkn⟩ with hi
  have hcs : (Finset.Iio i).card = k := by simp [hi]
  have hct : (Finset.Ici i).card = k := by
    rw [Fin.card_Ici]
    show 2 * k - k = k
    omega
  set S : KneserVertex (2 * k) k := ⟨Finset.Iio i, hcs⟩ with hS
  set T : KneserVertex (2 * k) k := ⟨Finset.Ici i, hct⟩ with hT
  have hdisj : Disjoint (Finset.Iio i) (Finset.Ici i) :=
    Finset.disjoint_left.2 fun a ha hb =>
      absurd (Finset.mem_Ici.1 hb) (not_le.2 (Finset.mem_Iio.1 ha))
  have hST : S ≠ T := by
    intro h
    have h1 : (Finset.Iio i) = (Finset.Ici i) := congrArg Subtype.val h
    have h2 : i ∈ Finset.Ici i := Finset.mem_Ici.2 le_rfl
    rw [← h1] at h2
    exact absurd (Finset.mem_Iio.1 h2) (lt_irrefl i)
  have hlower : (2 : ℕ∞) ≤ (kneserGraph (2 * k) k).chromaticNumber :=
    SimpleGraph.two_le_chromaticNumber_of_adj (u := S) (v := T) ⟨hST, hdisj⟩
  have h2 : 2 * k - 2 * k + 2 = 2 := by omega
  rw [h2] at hupper ⊢
  exact le_antisymm hupper (by exact_mod_cast hlower)

/-!
### The odd case `n = 2k + 1`

Here `KG_{2k+1,k}` contains an odd cycle of length `2k+1` (the "cyclic intervals"
`{j, j+1, …, j+k-1}` taken modulo `2k+1`, joined in steps of `k`), so it is not
`2`-colorable and its chromatic number is `3 = (2k+1) - 2k + 2`.
-/

/-- The cyclic interval `{j, j+1, …, j+k-1}` of `Fin (2k+1)`, taken modulo `2k+1`. -/
def cyclicBlock (k j : ℕ) : Finset (Fin (2 * k + 1)) :=
  Finset.image
    (fun t : Fin k => (⟨(j + t.val) % (2 * k + 1), Nat.mod_lt _ (by omega)⟩ : Fin (2 * k + 1)))
    Finset.univ

lemma mem_cyclicBlock {k j : ℕ} {x : Fin (2 * k + 1)} :
    x ∈ cyclicBlock k j ↔ ∃ t < k, x.val = (j + t) % (2 * k + 1) := by
  simp only [cyclicBlock, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨t.val, t.isLt, rfl⟩
  · rintro ⟨t, ht, hx⟩
    exact ⟨⟨t, ht⟩, by apply Fin.ext; simp [hx]⟩

private lemma mod_add_cancel {N x a b : ℕ} (ha : a < N) (hb : b < N)
    (h : (x + a) % N = (x + b) % N) : a = b :=
  (Nat.ModEq.add_left_cancel' x h).eq_of_lt_of_lt ha hb

lemma cyclicBlock_card (k j : ℕ) : (cyclicBlock k j).card = k := by
  rw [cyclicBlock, Finset.card_image_of_injective _ ?inj, Finset.card_univ, Fintype.card_fin]
  case inj =>
    intro a b hab
    have h : (j + a.val) % (2 * k + 1) = (j + b.val) % (2 * k + 1) := congrArg Fin.val hab
    exact Fin.ext (mod_add_cancel (N := 2 * k + 1) (by omega) (by omega) h)

lemma cyclicBlock_congr (k : ℕ) {j j' : ℕ} (h : j ≡ j' [MOD 2 * k + 1]) :
    cyclicBlock k j = cyclicBlock k j' := by
  ext x
  simp only [mem_cyclicBlock]
  constructor <;> rintro ⟨t, ht, hx⟩ <;> refine ⟨t, ht, ?_⟩
  · rw [hx]; exact h.add_right t
  · rw [hx]; exact h.symm.add_right t

lemma cyclicBlock_disjoint (k j : ℕ) :
    Disjoint (cyclicBlock k j) (cyclicBlock k (j + k)) := by
  rw [Finset.disjoint_left]
  rintro x hx hx'
  rw [mem_cyclicBlock] at hx hx'
  obtain ⟨a, ha, hxa⟩ := hx
  obtain ⟨b, hb, hxb⟩ := hx'
  have h : (j + a) % (2 * k + 1) = (j + (k + b)) % (2 * k + 1) := by
    rw [← hxa, hxb]; ring_nf
  have := mod_add_cancel (N := 2 * k + 1) (x := j) (by omega) (by omega) h
  omega

/-- The vertex of `KG_{2k+1,k}` given by the cyclic interval starting at `j`. -/
def cyclicVertex (k j : ℕ) : KneserVertex (2 * k + 1) k :=
  ⟨cyclicBlock k j, cyclicBlock_card k j⟩

lemma cyclicVertex_adj (k j : ℕ) (hk : 1 ≤ k) :
    (kneserGraph (2 * k + 1) k).Adj (cyclicVertex k j) (cyclicVertex k (j + k)) := by
  refine ⟨?_, cyclicBlock_disjoint k j⟩
  intro h
  have h1 : cyclicBlock k j = cyclicBlock k (j + k) := congrArg Subtype.val h
  have hd := cyclicBlock_disjoint k j
  rw [← h1] at hd
  have hne : (cyclicBlock k j).Nonempty := by
    rw [← Finset.card_pos, cyclicBlock_card]; omega
  obtain ⟨x, hx⟩ := hne
  exact (Finset.disjoint_left.mp hd hx) hx

/-- `KG_{2k+1,k}` is not `2`-colorable, because the cyclic intervals form an odd cycle. -/
theorem kneser_not_colorable_two (k : ℕ) (hk : 1 ≤ k) :
    ¬ (kneserGraph (2 * k + 1) k).Colorable 2 := by
  rintro ⟨C⟩
  set g : ℕ → Fin 2 := fun t => C (cyclicVertex k (t * k)) with hg
  have hstep : ∀ t, g t ≠ g (t + 1) := by
    intro t
    have ht : (t + 1) * k = t * k + k := by ring
    simpa [hg, ht] using C.valid (cyclicVertex_adj k (t * k) hk)
  have key : ∀ x y z : Fin 2, x ≠ y → y ≠ z → x = z := by decide
  have heven : ∀ t, g (2 * t) = g 0 := by
    intro t
    induction t with
    | zero => rfl
    | succ m ih =>
      have h1 : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
      rw [h1, ← ih]
      exact (key _ _ _ (hstep (2 * m)) (hstep (2 * m + 1))).symm
  have hlast : g (2 * k + 1) = g 0 := by
    have hv : cyclicVertex k ((2 * k + 1) * k) = cyclicVertex k (0 * k) := by
      unfold cyclicVertex
      congr 1
      apply cyclicBlock_congr
      show ((2 * k + 1) * k) % (2 * k + 1) = (0 * k) % (2 * k + 1)
      simp [Nat.mul_mod_left, Nat.mul_comm]
    simp [hg, hv]
  exact hstep (2 * k) (by rw [heven k, ← hlast])

/-- For `n = 2k + 1` (with `k ≥ 1`) the chromatic number of the Kneser graph is `3`. -/
theorem kneser_chromaticNumber_of_n_eq_two_mul_k_add_one (k : ℕ) (hk : 1 ≤ k) :
    (kneserGraph (2 * k + 1) k).chromaticNumber = (2 * k + 1 - 2 * k + 2 : ℕ) := by
  have h3 : 2 * k + 1 - 2 * k + 2 = 3 := by omega
  rw [h3]
  have hupper : (kneserGraph (2 * k + 1) k).chromaticNumber ≤ ((3 : ℕ) : ℕ∞) := by
    have := (kneser_colorable (2 * k + 1) k hk (by omega)).chromaticNumber_le
    rwa [h3] at this
  have hlower : ((3 : ℕ) : ℕ∞) ≤ (kneserGraph (2 * k + 1) k).chromaticNumber := by
    by_contra hcon
    have hlt : (kneserGraph (2 * k + 1) k).chromaticNumber < ((3 : ℕ) : ℕ∞) := not_le.1 hcon
    have hle : (kneserGraph (2 * k + 1) k).chromaticNumber ≤ ((2 : ℕ) : ℕ∞) := by
      have : ((3 : ℕ) : ℕ∞) = ((2 : ℕ) : ℕ∞) + 1 := by norm_num
      rw [this] at hlt
      exact Order.le_of_lt_add_one hlt
    exact kneser_not_colorable_two k hk (SimpleGraph.chromaticNumber_le_iff_colorable.1 hle)
  exact le_antisymm hupper hlower

/-- **Lovász–Kneser theorem (base cases).**

Lovász's theorem states that the chromatic number of the Kneser graph `KG_{n,k}`
(vertices: the `k`-subsets of an `n`-set; edges: pairs of disjoint `k`-subsets) equals
`n - 2k + 2` whenever `n ≥ 2k ≥ 2`; the lower bound is the deep direction, proved via the
Borsuk–Ulam theorem.

Here we prove the statement in its base cases `k = 1` (where `KG_{n,1}` is the complete
graph `K_n`), `n = 2k` (where `KG_{2k,k}` is a perfect matching) and `n = 2k + 1` (the odd
Kneser graphs, which contain an odd cycle and hence need `3` colors).  The easy upper bound
`χ(KG_{n,k}) ≤ n - 2k + 2` is proved in full generality in `Frontier.kneser_colorable`. -/
theorem lovasz_kneser (n k : ℕ) (hk : 1 ≤ k) (h2k : 2 * k ≤ n)
    (hbase : k = 1 ∨ n = 2 * k ∨ n = 2 * k + 1) :
    (kneserGraph n k).chromaticNumber = (n - 2 * k + 2 : ℕ) := by
  rcases hbase with rfl | rfl | rfl
  · exact kneser_chromaticNumber_of_k_eq_one n (by omega)
  · exact kneser_chromaticNumber_of_n_eq_two_mul_k k hk
  · exact kneser_chromaticNumber_of_n_eq_two_mul_k_add_one k hk

end Frontier

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

