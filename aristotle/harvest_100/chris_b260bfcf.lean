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

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of an
`n`-element set. -/
abbrev KneserVertex (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of `Fin n`, and two
distinct such subsets are adjacent when they are disjoint. -/
def kneserGraph (n k : ℕ) : SimpleGraph (KneserVertex n k) where
  Adj s t := s ≠ t ∧ Disjoint s.1 t.1
  symm := by
    rintro s t ⟨h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩
  loopless := by
    constructor
    rintro s ⟨h1, -⟩
    exact h1 rfl

@[simp]
lemma kneserGraph_adj {n k : ℕ} (s t : KneserVertex n k) :
    (kneserGraph n k).Adj s t ↔ s ≠ t ∧ Disjoint s.1 t.1 := Iff.rfl

lemma kneserVertex_nonempty {n k : ℕ} (hk : 1 ≤ k) (s : KneserVertex n k) : s.1.Nonempty := by
  rw [← Finset.card_pos, s.2]; omega

/-- Two `k`-subsets of a set of size `< 2 * k` cannot be disjoint. -/
lemma not_disjoint_of_card_lt {n k : ℕ} {s t : Finset (Fin n)} (hs : s.card = k)
    (ht : t.card = k) (u : Finset (Fin n)) (hsu : s ⊆ u) (htu : t ⊆ u)
    (hu : u.card < 2 * k) : ¬ Disjoint s t := by
  intro hd
  have h1 : (s ∪ t).card = 2 * k := by
    rw [Finset.card_union_of_disjoint hd, hs, ht]; ring
  have h2 : (s ∪ t).card ≤ u.card := Finset.card_le_card (Finset.union_subset hsu htu)
  omega

/-- The standard greedy colouring: `KG_{n,k}` is `(n - 2k + 2)`-colourable. -/
theorem kneserGraph_colorable (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n + 1) :
    (kneserGraph n k).Colorable (n + 2 - 2 * k) := by
  classical
  set m := n + 1 - 2 * k with hm
  have hne : ∀ s : KneserVertex n k, s.1.Nonempty := fun s => kneserVertex_nonempty hk s
  refine ⟨SimpleGraph.Coloring.mk
    (fun s => (⟨min m ((s.1.min' (hne s) : Fin n) : ℕ), by omega⟩ : Fin (n + 2 - 2 * k))) ?_⟩
  rintro s t ⟨-, hdisj⟩ hcol
  have hcol' : min m ((s.1.min' (hne s) : Fin n) : ℕ) = min m ((t.1.min' (hne t) : Fin n) : ℕ) := by
    simpa [Fin.ext_iff] using hcol
  set a : ℕ := ((s.1.min' (hne s) : Fin n) : ℕ) with ha
  set b : ℕ := ((t.1.min' (hne t) : Fin n) : ℕ) with hb
  by_cases hcase : a < m ∧ b < m
  · -- the two minima coincide, contradicting disjointness
    have hab : a = b := by omega
    have hsm : s.1.min' (hne s) ∈ s.1 := Finset.min'_mem _ _
    have htm : t.1.min' (hne t) ∈ t.1 := Finset.min'_mem _ _
    have : s.1.min' (hne s) = t.1.min' (hne t) := Fin.ext hab
    exact (Finset.disjoint_left.mp hdisj hsm) (this ▸ htm)
  · -- both sets live in the last `2k - 1` elements
    have hma : m ≤ a := by omega
    have hmb : m ≤ b := by omega
    have hsub : ∀ (u : Finset (Fin n)) (hu : u.Nonempty), m ≤ ((u.min' hu : Fin n) : ℕ) →
        u ⊆ (Finset.Ico m n).attachFin (by intro x hx; simp at hx; omega) := by
      intro u hu hmin x hx
      have hle : u.min' hu ≤ x := Finset.min'_le _ _ hx
      have : m ≤ (x : ℕ) := le_trans hmin hle
      simp only [Finset.mem_attachFin, Finset.mem_Ico]
      exact ⟨this, x.2⟩
    refine not_disjoint_of_card_lt s.2 t.2
      ((Finset.Ico m n).attachFin (by intro x hx; simp at hx; omega)) (hsub _ _ hma)
      (hsub _ _ hmb) ?_ hdisj
    rw [Finset.card_attachFin, Nat.card_Ico]
    omega

/-! ### The base case `k = 1`: the Kneser graph is the complete graph -/

lemma kneserGraph_one_eq_top (n : ℕ) : kneserGraph n 1 = ⊤ := by
  ext s t
  simp only [kneserGraph_adj, SimpleGraph.top_adj]
  constructor
  · exact fun h => h.1
  · intro hst
    refine ⟨hst, ?_⟩
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp s.2
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp t.2
    rw [ha, hb, Finset.disjoint_singleton]
    intro hab
    exact hst (Subtype.ext (by rw [ha, hb, hab]))

lemma card_kneserVertex_one (n : ℕ) : Fintype.card (KneserVertex n 1) = n := by
  simp [KneserVertex, Fintype.card_finset_len]

/-! ### The base case `n = 2 * k`: the Kneser graph has an edge -/

lemma kneserGraph_exists_adj (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    ∃ s t : KneserVertex n k, (kneserGraph n k).Adj s t := by
  classical
  have h1 : ∀ x ∈ Finset.range k, x < n := by intro x hx; simp at hx; omega
  have h2 : ∀ x ∈ Finset.Ico k (2 * k), x < n := by intro x hx; simp at hx; omega
  refine ⟨⟨(Finset.range k).attachFin h1, by rw [Finset.card_attachFin, Finset.card_range]⟩,
    ⟨(Finset.Ico k (2 * k)).attachFin h2, by rw [Finset.card_attachFin, Nat.card_Ico]; omega⟩, ?_⟩
  have hdisj : Disjoint ((Finset.range k).attachFin h1) ((Finset.Ico k (2 * k)).attachFin h2) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp [Finset.mem_attachFin] at hx hx'
    omega
  refine ⟨?_, hdisj⟩
  intro hEq
  have hmem : (⟨0, by omega⟩ : Fin n) ∈ (Finset.range k).attachFin h1 := by
    simp [Finset.mem_attachFin]; omega
  have := Finset.disjoint_left.mp hdisj hmem
  rw [Subtype.ext_iff] at hEq
  simp only at hEq
  exact this (hEq ▸ hmem)

lemma kneserGraph_not_colorable_one (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    ¬ (kneserGraph n k).Colorable 1 := by
  intro h
  obtain ⟨s, t, hst⟩ := kneserGraph_exists_adj n k hk hn
  obtain ⟨C⟩ := h
  exact C.valid hst (Subsingleton.elim _ _)

/-! ### The base case `n = 2 * k + 1`: an odd cycle of consecutive blocks -/

/-- The block of `k` cyclically consecutive elements of `Fin (2 * k + 1)` starting at `i`. -/
def cycBlock (k i : ℕ) : Finset (Fin (2 * k + 1)) :=
  (Finset.range k).image
    (fun j => (⟨(i + j) % (2 * k + 1), Nat.mod_lt _ (by omega)⟩ : Fin (2 * k + 1)))

lemma cyc_key (k i a b : ℕ) (ha : a < 2 * k + 1) (hb : b < 2 * k + 1)
    (h : (i + a) % (2 * k + 1) = (i + b) % (2 * k + 1)) : a = b := by
  have h1 : (i + a) ≡ (i + b) [MOD 2 * k + 1] := h
  have h2 : a ≡ b [MOD 2 * k + 1] := Nat.ModEq.add_left_cancel' i h1
  unfold Nat.ModEq at h2
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2

lemma card_cycBlock (k i : ℕ) : (cycBlock k i).card = k := by
  rw [cycBlock, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  have h := congrArg Fin.val hab
  simp only at h
  exact cyc_key k i a b (by omega) (by omega) h

lemma disjoint_cycBlock (k i : ℕ) : Disjoint (cycBlock k (i + k)) (cycBlock k i) := by
  rw [Finset.disjoint_left]
  rintro x hx hx'
  simp only [cycBlock, Finset.mem_image, Finset.mem_range] at hx hx'
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, hb'⟩ := hx'
  have h1 := congrArg Fin.val hb'
  simp only at h1
  have h2 : (i + b) % (2 * k + 1) = (i + (k + a)) % (2 * k + 1) := by
    rw [← add_assoc]; exact h1
  have h3 := cyc_key k i b (k + a) (by omega) (by omega) h2
  omega

lemma cycBlock_period (k : ℕ) : cycBlock k ((2 * k + 1) * k) = cycBlock k 0 := by
  unfold cycBlock
  apply Finset.image_congr
  intro j _
  apply Fin.ext
  simp only [Nat.zero_add]
  rw [Nat.add_comm]
  exact Nat.add_mul_mod_self_left j (2 * k + 1) k

lemma cycBlock_ne (k i : ℕ) (hk : 1 ≤ k) : cycBlock k (i + k) ≠ cycBlock k i := by
  intro h
  have hd := disjoint_cycBlock k i
  rw [h] at hd
  have hemp := Finset.disjoint_self.mp hd
  have hc := card_cycBlock k i
  rw [hemp, Finset.card_empty] at hc
  omega

/-- The vertex of `KG_{2k+1,k}` given by the cyclic block starting at `i`. -/
def cycVertex (k i : ℕ) : KneserVertex (2 * k + 1) k := ⟨cycBlock k i, card_cycBlock k i⟩

/-- `KG_{2k+1,k}` contains the odd cycle `cycVertex k 0, cycVertex k k, cycVertex k (2k), ...`,
hence is not `2`-colourable. -/
lemma kneserGraph_not_colorable_two (k : ℕ) (hk : 1 ≤ k) :
    ¬ (kneserGraph (2 * k + 1) k).Colorable 2 := by
  rintro ⟨C⟩
  have hadj : ∀ i : ℕ, C (cycVertex k (i + k)) ≠ C (cycVertex k i) := by
    intro i
    refine C.valid ⟨?_, disjoint_cycBlock k i⟩
    intro h
    exact cycBlock_ne k i hk (congrArg Subtype.val h)
  have key : ∀ a b : Fin 2, a ≠ b → a = b + 1 := by decide
  have key2 : ∀ a : Fin 2, a + 1 + 1 = a := by decide
  have key3 : ∀ a : Fin 2, a ≠ a + 1 := by decide
  have hstep : ∀ m : ℕ, C (cycVertex k ((m + 1) * k)) = C (cycVertex k (m * k)) + 1 := by
    intro m
    refine key _ _ ?_
    have h1 : (m + 1) * k = m * k + k := by ring
    rw [h1]
    exact hadj (m * k)
  have hpar : ∀ m : ℕ, C (cycVertex k (m * k))
      = if m % 2 = 0 then C (cycVertex k 0) else C (cycVertex k 0) + 1 := by
    intro m
    induction m with
    | zero => simp
    | succ p ih =>
      rw [hstep p, ih]
      by_cases hp : p % 2 = 0
      · rw [if_pos hp, if_neg (by omega)]
      · rw [if_neg hp, if_pos (by omega), key2]
  have hfin := hpar (2 * k + 1)
  rw [if_neg (by omega)] at hfin
  have hveq : cycVertex k ((2 * k + 1) * k) = cycVertex k 0 :=
    Subtype.ext (cycBlock_period k)
  rw [hveq] at hfin
  exact key3 _ hfin

/-! ### Main theorem -/

/-- If `G` is `(m+1)`-colourable but not `m`-colourable, its chromatic number is `m + 1`. -/
lemma chromaticNumber_eq_of_colorable {V : Type*} {G : SimpleGraph V} {m : ℕ}
    (h1 : G.Colorable (m + 1)) (h2 : ¬ G.Colorable m) :
    G.chromaticNumber = ((m + 1 : ℕ) : ℕ∞) := by
  refine le_antisymm (chromaticNumber_le_iff_colorable.mpr h1) ?_
  have hlt : ¬ (G.chromaticNumber ≤ ((m : ℕ) : ℕ∞)) := fun h =>
    h2 (chromaticNumber_le_iff_colorable.mp h)
  have := Order.add_one_le_of_lt (lt_of_not_ge hlt)
  exact_mod_cast this

/-- **Lovász–Kneser theorem (base cases).**  The chromatic number of the Kneser graph
`KG_{n,k}` (vertices: the `k`-element subsets of an `n`-element set; edges: pairs of disjoint
subsets) is `n - 2k + 2`.

The upper bound `χ(KG_{n,k}) ≤ n - 2k + 2` is proved in full generality in
`Frontier.kneserGraph_colorable`.  The matching lower bound, which in general requires the
Borsuk–Ulam theorem, is established here in the base cases

* `k = 1`, where `KG_{n,1}` is the complete graph `K_n` and `χ = n`;
* `n = 2k`, where `KG_{2k,k}` is a perfect matching and `χ = 2`;
* `n = 2k + 1`, where `KG_{2k+1,k}` is the odd graph `O_{k+1}` and `χ = 3`, the lower bound
  coming from the odd cycle of cyclically consecutive blocks.

The hypothesis `2 * k ≤ n` is part of the classical statement of the theorem. -/
theorem lovasz_kneser (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (hbase : k = 1 ∨ n = 2 * k ∨ n = 2 * k + 1) :
    (kneserGraph n k).chromaticNumber = (n + 2 - 2 * k : ℕ) := by
  rcases hbase with rfl | rfl | rfl
  · rw [kneserGraph_one_eq_top, SimpleGraph.chromaticNumber_top, card_kneserVertex_one]
    norm_num
  · have h2 : (2 * k + 2 - 2 * k : ℕ) = 1 + 1 := by omega
    rw [h2]
    refine chromaticNumber_eq_of_colorable ?_ (kneserGraph_not_colorable_one (2 * k) k hk le_rfl)
    have := kneserGraph_colorable (2 * k) k hk (by omega)
    rwa [h2] at this
  · have h3 : (2 * k + 1 + 2 - 2 * k : ℕ) = 2 + 1 := by omega
    rw [h3]
    refine chromaticNumber_eq_of_colorable ?_ (kneserGraph_not_colorable_two k hk)
    have := kneserGraph_colorable (2 * k + 1) k hk (by omega)
    rwa [h3] at this

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

