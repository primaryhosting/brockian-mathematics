import Mathlib
/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

/-- Vertices of the Kneser graph `KG_{n,k}`: the `k`-element subsets of an `n`-element set. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-subsets of `Fin n`, and two
distinct vertices are adjacent when the corresponding sets are disjoint. -/
def kneserGraph (n k : ℕ) : SimpleGraph (KneserVertex n k) where
  Adj s t := Disjoint s.1 t.1 ∧ s ≠ t
  symm := by
    rintro s t ⟨h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩
  loopless := ⟨by
    rintro s ⟨-, h2⟩
    exact h2 rfl⟩

lemma kneserGraph_adj {n k : ℕ} (s t : KneserVertex n k) :
    (kneserGraph n k).Adj s t ↔ (Disjoint s.1 t.1 ∧ s ≠ t) := Iff.rfl

lemma vertex_nonempty {n k : ℕ} (hk : 1 ≤ k) (s : KneserVertex n k) : s.1.Nonempty :=
  Finset.card_pos.mp (by rw [s.2]; omega)

/-- The standard `(n - 2k + 2)`-coloring of the Kneser graph: a `k`-set `s` gets the color
`min (min s) (n - 2k + 1)`.  The colour classes `{s | min s = i}` for `i < n - 2k + 1` are
intersecting, and the last class consists of the `k`-subsets of the `(2k-1)`-element set
`{n - 2k + 1, …, n - 1}`, which is intersecting as well. -/
lemma kneser_colorable (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (kneserGraph n k).Colorable (n - 2 * k + 2) := by
  set m := n - 2 * k + 1 with hm
  refine ⟨⟨fun s => ⟨min ((s.1.min' (vertex_nonempty hk s)) : Fin n).val m, by omega⟩, ?_⟩⟩
  rintro s t ⟨hdisj, -⟩ heq
  simp only [Fin.mk.injEq] at heq
  set a := ((s.1.min' (vertex_nonempty hk s)) : Fin n) with ha
  set b := ((t.1.min' (vertex_nonempty hk t)) : Fin n) with hb
  by_cases hlt : a.val < m
  · -- Both minima are equal to a common element below `m`, contradicting disjointness.
    have hb' : b.val = a.val := by omega
    have has : a ∈ s.1 := Finset.min'_mem _ _
    have hbt : b ∈ t.1 := Finset.min'_mem _ _
    have hab : a = b := Fin.ext hb'.symm
    exact (Finset.disjoint_left.mp hdisj has) (hab ▸ hbt)
  · -- Both sets live inside `{m, …, n-1}`, of size `2k - 1 < 2k`.
    push_neg at hlt
    have hbm : m ≤ b.val := by omega
    have hsub : (s.1 ∪ t.1).image Fin.val ⊆ Finset.Ico m n := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_union] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      refine Finset.mem_Ico.mpr ⟨?_, y.isLt⟩
      rcases hy with hy | hy
      · exact le_trans hlt (Finset.min'_le _ _ hy)
      · exact le_trans hbm (Finset.min'_le _ _ hy)
    have hcard : ((s.1 ∪ t.1).image Fin.val).card = 2 * k := by
      rw [Finset.card_image_of_injective _ Fin.val_injective,
        Finset.card_union_of_disjoint hdisj, s.2, t.2]
      omega
    have hle := Finset.card_le_card hsub
    rw [hcard, Nat.card_Ico] at hle
    omega

/-- The upper bound of the Lovász–Kneser theorem, valid for all `n ≥ 2k ≥ 2`. -/
lemma kneser_chromaticNumber_le (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (kneserGraph n k).chromaticNumber ≤ (n - 2 * k + 2 : ℕ) :=
  SimpleGraph.chromaticNumber_le_iff_colorable.mpr (kneser_colorable n k hk hn)

/-- For `k = 1` the Kneser graph is the complete graph on the `n` singletons. -/
lemma kneserGraph_one_eq_top (n : ℕ) : kneserGraph n 1 = ⊤ := by
  ext s t
  simp only [SimpleGraph.top_adj]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro hst
    refine ⟨?_, hst⟩
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp s.2
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp t.2
    rw [ha, hb, Finset.disjoint_singleton]
    intro hab
    exact hst (Subtype.ext (by rw [ha, hb, hab]))

/-- `KG_{n,1}` is the complete graph `K_n`, so its chromatic number is `n = n - 2·1 + 2`. -/
lemma lovasz_kneser_one (n : ℕ) (hn : 2 ≤ n) :
    (kneserGraph n 1).chromaticNumber = (n - 2 * 1 + 2 : ℕ) := by
  rw [kneserGraph_one_eq_top, SimpleGraph.chromaticNumber_top]
  have hcard : Fintype.card (KneserVertex n 1) = n := by
    rw [Fintype.card_finset_len]
    simp
  rw [hcard]
  congr 1
  omega

/-- `KG_{2k,k}` has an edge: the first `k` and the last `k` elements of `Fin (2k)`. -/
lemma kneser_two_k_has_edge (k : ℕ) (hk : 1 ≤ k) :
    ∃ s t : KneserVertex (2 * k) k, (kneserGraph (2 * k) k).Adj s t := by
  have h1 : ∀ m ∈ Finset.range k, m < 2 * k := by
    intro m hm
    simp only [Finset.mem_range] at hm
    omega
  have h2 : ∀ m ∈ Finset.Ico k (2 * k), m < 2 * k := by
    intro m hm
    simp only [Finset.mem_Ico] at hm
    omega
  refine ⟨⟨(Finset.range k).attachFin h1, by rw [Finset.card_attachFin, Finset.card_range]⟩,
    ⟨(Finset.Ico k (2 * k)).attachFin h2, by
      rw [Finset.card_attachFin, Nat.card_Ico]; omega⟩, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_attachFin, Finset.mem_range] at ha
    rw [Finset.mem_attachFin, Finset.mem_Ico] at hb
    omega
  · intro h
    have hv := congrArg Subtype.val h
    simp only at hv
    have h0 : (⟨0, by omega⟩ : Fin (2 * k)) ∈ (Finset.range k).attachFin h1 := by
      rw [Finset.mem_attachFin, Finset.mem_range]
      exact hk
    rw [hv, Finset.mem_attachFin, Finset.mem_Ico] at h0
    have h0' : k ≤ 0 := h0.1
    omega

lemma kneser_two_k_not_colorable_one (k : ℕ) (hk : 1 ≤ k) :
    ¬ (kneserGraph (2 * k) k).Colorable 1 := by
  rintro ⟨C⟩
  obtain ⟨s, t, hst⟩ := kneser_two_k_has_edge k hk
  exact C.valid hst (Subsingleton.elim _ _)

/-- For `n = 2k` (with `k ≥ 1`) the Kneser graph is a perfect matching, of chromatic number
`2 = n - 2k + 2`. -/
lemma lovasz_kneser_two_k (k : ℕ) (hk : 1 ≤ k) :
    (kneserGraph (2 * k) k).chromaticNumber = (2 * k - 2 * k + 2 : ℕ) := by
  have hupper : (kneserGraph (2 * k) k).chromaticNumber ≤ (2 * k - 2 * k + 2 : ℕ) :=
    kneser_chromaticNumber_le (2 * k) k hk le_rfl
  have hlower : (2 : ℕ∞) ≤ (kneserGraph (2 * k) k).chromaticNumber := by
    have hnot : ¬ (kneserGraph (2 * k) k).chromaticNumber ≤ (1 : ℕ) := fun h =>
      kneser_two_k_not_colorable_one k hk (SimpleGraph.chromaticNumber_le_iff_colorable.mp h)
    have := Order.add_one_le_of_lt (not_le.mp (by simpa using hnot))
    simpa using this
  have h2 : ((2 * k - 2 * k + 2 : ℕ) : ℕ∞) = 2 := by
    simp
  rw [h2] at hupper ⊢
  exact le_antisymm hupper hlower

/-! ### The odd graphs `KG_{2k+1,k}`

For `n = 2k+1` the Kneser graph contains the cycle `V 0, V 1, …, V (2k+1) = V 0` of odd length
`2k+1`, where `V j` is the set of `k` consecutive residues `jk, jk+1, …, jk+k-1` modulo `2k+1`.
An odd closed walk obstructs `2`-colourability, so `χ(KG_{2k+1,k}) = 3 = n - 2k + 2`. -/

/-- A graph carrying a closed walk of odd length is not `2`-colourable. -/
theorem not_colorable_two_of_odd_closed_walk {V : Type*} {G : SimpleGraph V}
    (f : ℕ → V) (N : ℕ) (hadj : ∀ j < N, G.Adj (f j) (f (j + 1)))
    (hcl : f N = f 0) (hodd : Odd N) : ¬ G.Colorable 2 := by
  rintro ⟨C⟩
  let D : G.Coloring (ZMod 2) := C
  have key : ∀ j ≤ N, D (f j) = D (f 0) + (j : ZMod 2) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have hne : D (f i) ≠ D (f (i + 1)) := D.valid (hadj i (by omega))
      have hstep : D (f (i + 1)) = D (f i) + 1 := by
        revert hne
        generalize D (f i) = a
        generalize D (f (i + 1)) = b
        revert a b
        decide
      rw [hstep, ih (by omega)]
      push_cast
      ring
  obtain ⟨m, hm⟩ := hodd
  have h1 : ((N : ℕ) : ZMod 2) = 1 := by
    subst hm
    have h : ((2 * m + 1 : ℕ) : ZMod 2) = (2 : ZMod 2) * m + 1 := by push_cast; ring
    rw [h, show (2 : ZMod 2) = 0 from rfl]
    ring
  have hN := key N le_rfl
  rw [hcl, h1] at hN
  exact absurd hN (by generalize D (f 0) = a; revert a; decide)

/-- The residue of `x` modulo `2k+1`, as an element of `Fin (2k+1)`. -/
def oddElt (k x : ℕ) : Fin (2 * k + 1) := ⟨x % (2 * k + 1), Nat.mod_lt _ (by omega)⟩

lemma oddElt_eq_iff (k x y : ℕ) :
    oddElt k x = oddElt k y ↔ x % (2 * k + 1) = y % (2 * k + 1) := by
  simp [oddElt, Fin.ext_iff]

/-- The `j`-th vertex of the canonical odd cycle in `KG_{2k+1,k}`: the `k` consecutive
residues `jk, jk+1, …, jk+k-1` modulo `2k+1`. -/
def oddCycVert (k j : ℕ) : Finset (Fin (2 * k + 1)) :=
  (Finset.range k).image (fun i => oddElt k (j * k + i))

lemma oddCycVert_card (k j : ℕ) : (oddCycVert k j).card = k := by
  rw [oddCycVert, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_range] at ha hb
  rw [oddElt_eq_iff] at hab
  have h : a ≡ b [MOD 2 * k + 1] := Nat.ModEq.add_left_cancel' (j * k) hab
  unfold Nat.ModEq at h
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h

lemma oddCycVert_disjoint (k j : ℕ) : Disjoint (oddCycVert k j) (oddCycVert k (j + 1)) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [oddCycVert, Finset.mem_image, Finset.mem_range] at hx hx'
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, hba⟩ := hx'
  rw [oddElt_eq_iff] at hba
  have h : (k + b) ≡ a [MOD 2 * k + 1] := by
    refine Nat.ModEq.add_left_cancel' (j * k) ?_
    unfold Nat.ModEq
    rw [← hba]
    ring_nf
  unfold Nat.ModEq at h
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  omega

lemma oddCycVert_period (k : ℕ) : oddCycVert k (2 * k + 1) = oddCycVert k 0 := by
  unfold oddCycVert
  apply Finset.image_congr
  intro i _
  rw [oddElt_eq_iff]
  simp

/-- The vertices of the canonical odd cycle in `KG_{2k+1,k}`. -/
def oddCyc (k j : ℕ) : KneserVertex (2 * k + 1) k := ⟨oddCycVert k j, oddCycVert_card k j⟩

lemma oddCyc_adj (k : ℕ) (hk : 1 ≤ k) (j : ℕ) :
    (kneserGraph (2 * k + 1) k).Adj (oddCyc k j) (oddCyc k (j + 1)) := by
  refine ⟨oddCycVert_disjoint k j, ?_⟩
  intro h
  have hd := oddCycVert_disjoint k j
  rw [show oddCycVert k (j + 1) = oddCycVert k j from congrArg Subtype.val h.symm,
    disjoint_self] at hd
  have := oddCycVert_card k j
  rw [hd] at this
  simp at this
  omega

lemma kneser_odd_not_colorable_two (k : ℕ) (hk : 1 ≤ k) :
    ¬ (kneserGraph (2 * k + 1) k).Colorable 2 :=
  not_colorable_two_of_odd_closed_walk (oddCyc k) (2 * k + 1)
    (fun j _ => oddCyc_adj k hk j)
    (Subtype.ext (oddCycVert_period k)) ⟨k, by ring⟩

/-- For `n = 2k+1` (with `k ≥ 1`) the Kneser graph is the odd graph `O_{k+1}`, whose chromatic
number is `3 = n - 2k + 2`. -/
lemma lovasz_kneser_two_k_add_one (k : ℕ) (hk : 1 ≤ k) :
    (kneserGraph (2 * k + 1) k).chromaticNumber = (2 * k + 1 - 2 * k + 2 : ℕ) := by
  have hupper : (kneserGraph (2 * k + 1) k).chromaticNumber ≤ (2 * k + 1 - 2 * k + 2 : ℕ) :=
    kneser_chromaticNumber_le (2 * k + 1) k hk (by omega)
  have hlower : (3 : ℕ∞) ≤ (kneserGraph (2 * k + 1) k).chromaticNumber := by
    have hnot : ¬ (kneserGraph (2 * k + 1) k).chromaticNumber ≤ (2 : ℕ) := fun h =>
      kneser_odd_not_colorable_two k hk (SimpleGraph.chromaticNumber_le_iff_colorable.mp h)
    have := Order.add_one_le_of_lt (not_le.mp (by simpa using hnot))
    simpa using this
  have h3 : ((2 * k + 1 - 2 * k + 2 : ℕ) : ℕ∞) = 3 := by
    have : (2 * k + 1 - 2 * k + 2 : ℕ) = 3 := by omega
    rw [this]
    rfl
  rw [h3] at hupper ⊢
  exact le_antisymm hupper hlower

/-- **Lovász–Kneser theorem** (base cases).  The chromatic number of the Kneser graph
`KG_{n,k}` equals `n - 2k + 2`.  Here we prove the statement in the base cases `k = 1`
(where `KG_{n,1}` is the complete graph `K_n`), `n = 2k` (where `KG_{2k,k}` is a perfect
matching) and `n = 2k + 1` (the odd graphs, where an odd cycle rules out `2`-colourings).
The general upper bound `χ(KG_{n,k}) ≤ n - 2k + 2` is `Frontier.kneser_chromaticNumber_le`;
the matching general lower bound is the hard direction, due to Lovász via the Borsuk–Ulam
theorem. -/
theorem lovasz_kneser (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (hbase : k = 1 ∨ n = 2 * k ∨ n = 2 * k + 1) :
    (kneserGraph n k).chromaticNumber = (n - 2 * k + 2 : ℕ) := by
  rcases hbase with rfl | rfl | rfl
  · exact lovasz_kneser_one n (by omega)
  · exact lovasz_kneser_two_k k hk
  · exact lovasz_kneser_two_k_add_one k hk

end Frontier

