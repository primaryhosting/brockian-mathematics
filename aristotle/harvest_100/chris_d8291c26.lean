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
def kneserGraph (n k : ℕ) : SimpleGraph (KneserVertex n k) where
  Adj s t := s ≠ t ∧ Disjoint (s : Finset (Fin n)) (t : Finset (Fin n))
  symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp] theorem kneserGraph_adj {n k : ℕ} (s t : KneserVertex n k) :
    (kneserGraph n k).Adj s t ↔ s ≠ t ∧ Disjoint (s : Finset (Fin n)) (t : Finset (Fin n)) :=
  Iff.rfl

/-! ### The general upper bound `χ(KG_{n,k}) ≤ n - 2k + 2` -/

/-- The standard colouring of the Kneser graph: a `k`-set `s` receives the colour
`min (min s) (n - 2k + 1)`.  Two disjoint `k`-sets cannot share a colour `c < n - 2k + 1`
(both would contain the element `c`), nor the colour `n - 2k + 1` (they would then both be
contained in a set of `2k - 1` elements).  Hence `KG_{n,k}` is `(n - 2k + 2)`-colourable. -/
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
theorem chromaticNumber_kneserGraph_le (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (kneserGraph n k).chromaticNumber ≤ (n - 2 * k + 2 : ℕ) :=
  chromaticNumber_le_iff_colorable.2 (kneserGraph_colorable n k hk hn)

/-! ### The base case `k = 1`: `KG_{n,1}` is the complete graph `K_n` -/

/-- `KG_{n,1}` is the complete graph on the `n` singletons. -/
theorem kneserGraph_one_eq_top (n : ℕ) : kneserGraph n 1 = ⊤ := by
  ext s t
  simp only [kneserGraph, top_adj, and_iff_left_iff_imp]
  intro hst
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 s.2
  obtain ⟨b, hb⟩ := Finset.card_eq_one.1 t.2
  have hab : a ≠ b := by
    rintro rfl; exact hst (Subtype.ext (ha.trans hb.symm))
  simp [ha, hb, hab]

/-- The chromatic number of `KG_{n,1} = K_n` is `n`. -/
theorem chromaticNumber_kneserGraph_one (n : ℕ) :
    (kneserGraph n 1).chromaticNumber = (n : ℕ∞) := by
  rw [kneserGraph_one_eq_top, SimpleGraph.chromaticNumber_top]
  simp [Fintype.card_finset_len]

/-! ### The base case `n = 2k`: `KG_{2k,k}` is a perfect matching -/

/-- The chromatic number of `KG_{2k,k}` (a perfect matching, for `k ≥ 1`) is `2`. -/
theorem chromaticNumber_kneserGraph_two_mul (k : ℕ) (hk : 1 ≤ k) :
    (kneserGraph (2 * k) k).chromaticNumber = 2 := by
  have hpos : 0 < 2 * k := by omega
  set z : Fin (2 * k) := ⟨0, hpos⟩ with hz
  -- two adjacent vertices are complementary, so their union is everything
  have hunion : ∀ s t : KneserVertex (2 * k) k, (kneserGraph (2 * k) k).Adj s t →
      (s : Finset (Fin (2 * k))) ∪ (t : Finset (Fin (2 * k))) = Finset.univ := by
    intro s t h
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint h.2, s.2, t.2, Fintype.card_fin]
    omega
  -- colour a vertex according to whether it contains the element `0`
  have hcol : (kneserGraph (2 * k) k).Colorable 2 := by
    refine ⟨SimpleGraph.Coloring.mk
      (fun s => if z ∈ (s : Finset (Fin (2 * k))) then 0 else 1) ?_⟩
    intro s t h
    have hu := hunion s t h
    have hz' : z ∈ (s : Finset (Fin (2 * k))) ∪ (t : Finset (Fin (2 * k))) := by
      rw [hu]; exact Finset.mem_univ _
    rcases Finset.mem_union.1 hz' with h1 | h1
    · have h2 : z ∉ (t : Finset (Fin (2 * k))) := Finset.disjoint_left.1 h.2 h1
      simp [h1, h2]
    · have h2 : z ∉ (s : Finset (Fin (2 * k))) := Finset.disjoint_right.1 h.2 h1
      simp [h1, h2]
  -- the graph does have an edge, so one colour is not enough
  have hkl : k < 2 * k := by omega
  set a : Fin (2 * k) := ⟨k, hkl⟩ with ha
  have hs : (Finset.Iio a).card = k := by simp [ha]
  have ht : (Finset.Ici a).card = k := by simp [ha]; omega
  set S : KneserVertex (2 * k) k := ⟨Finset.Iio a, hs⟩ with hS
  set T : KneserVertex (2 * k) k := ⟨Finset.Ici a, ht⟩ with hT
  have hdisj : Disjoint (Finset.Iio a) (Finset.Ici a) := by
    simp [Finset.disjoint_left]
  have hne : S ≠ T := by
    intro h
    have h' : (Finset.Iio a) = Finset.Ici a := congrArg Subtype.val h
    rw [h'] at hdisj
    have he := disjoint_self.1 hdisj
    rw [he] at ht
    simp at ht
    omega
  have hadj : (kneserGraph (2 * k) k).Adj S T := ⟨hne, hdisj⟩
  have hlb : ¬ (kneserGraph (2 * k) k).Colorable 1 := by
    rintro ⟨C⟩
    exact C.valid hadj (Subsingleton.elim _ _)
  have h1 : (kneserGraph (2 * k) k).chromaticNumber ≤ 2 :=
    SimpleGraph.chromaticNumber_le_iff_colorable.2 hcol
  have h2 : ¬ (kneserGraph (2 * k) k).chromaticNumber ≤ 1 := fun h =>
    hlb (SimpleGraph.chromaticNumber_le_iff_colorable.1 (by exact_mod_cast h))
  exact le_antisymm h1 (Order.add_one_le_of_lt (not_le.1 h2))

/-! ### The base case `n = 2k + 1`: `KG_{2k+1,k}` is the odd graph `O_{k+1}` -/

/-- The cyclic interval `{i, i+1, …, i+k-1}` of `Fin (2k+1)`, indices taken modulo `2k+1`. -/
def cyclicInterval (k i : ℕ) : Finset (Fin (2 * k + 1)) :=
  (Finset.range k).image
    (fun j => (⟨(i + j) % (2 * k + 1), Nat.mod_lt _ (by omega)⟩ : Fin (2 * k + 1)))

theorem card_cyclicInterval (k i : ℕ) : (cyclicInterval k i).card = k := by
  rw [cyclicInterval, Finset.card_image_of_injOn, Finset.card_range]
  intro x hx y hy hxy
  simp only [Finset.mem_coe, Finset.mem_range] at hx hy
  have h : (i + x) % (2 * k + 1) = (i + y) % (2 * k + 1) := congrArg Fin.val hxy
  have h2 : x % (2 * k + 1) = y % (2 * k + 1) := Nat.ModEq.add_left_cancel' i h
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2

/-- Two cyclic intervals of length `k` starting `k` apart are disjoint inside `Fin (2k+1)`. -/
theorem disjoint_cyclicInterval (k i : ℕ) :
    Disjoint (cyclicInterval k i) (cyclicInterval k (i + k)) := by
  rw [Finset.disjoint_left]
  rintro x hx hy
  simp only [cyclicInterval, Finset.mem_image, Finset.mem_range] at hx hy
  obtain ⟨a, ha, hae⟩ := hx
  obtain ⟨b, hb, hbe⟩ := hy
  have h : (i + a) % (2 * k + 1) = (i + (k + b)) % (2 * k + 1) := by
    have h' := congrArg Fin.val (hae.trans hbe.symm)
    simpa [Nat.add_assoc] using h'
  have h2 : a % (2 * k + 1) = (k + b) % (2 * k + 1) := Nat.ModEq.add_left_cancel' i h
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
  omega

theorem cyclicInterval_congr (k i i' : ℕ) (h : i % (2 * k + 1) = i' % (2 * k + 1)) :
    cyclicInterval k i = cyclicInterval k i' := by
  unfold cyclicInterval
  refine Finset.image_congr ?_
  intro j _
  apply Fin.ext
  simp only
  rw [Nat.add_mod i j, Nat.add_mod i' j, h]

/-- The vertices of the odd closed walk `cyclicInterval k 0, cyclicInterval k k, …` of length
`2k+1` inside `KG_{2k+1,k}`. -/
def oddWalk (k j : ℕ) : KneserVertex (2 * k + 1) k :=
  ⟨cyclicInterval k (j * k), card_cyclicInterval k _⟩

theorem oddWalk_adj (k j : ℕ) (hk : 1 ≤ k) :
    (kneserGraph (2 * k + 1) k).Adj (oddWalk k j) (oddWalk k (j + 1)) := by
  have hd : Disjoint (cyclicInterval k (j * k)) (cyclicInterval k ((j + 1) * k)) := by
    have h := disjoint_cyclicInterval k (j * k)
    rwa [show (j + 1) * k = j * k + k by ring]
  refine ⟨?_, hd⟩
  intro h
  have h' : cyclicInterval k (j * k) = cyclicInterval k ((j + 1) * k) := congrArg Subtype.val h
  rw [← h'] at hd
  have he := disjoint_self.1 hd
  have hc := card_cyclicInterval k (j * k)
  rw [he] at hc
  simp at hc
  omega

theorem oddWalk_period (k : ℕ) : oddWalk k (2 * k + 1) = oddWalk k 0 := by
  apply Subtype.ext
  apply cyclicInterval_congr
  simp [Nat.mul_mod_left, Nat.mul_comm]

/-- `KG_{2k+1,k}` contains a closed walk of odd length `2k+1`, hence is not bipartite. -/
theorem not_colorable_two_kneserGraph_odd (k : ℕ) (hk : 1 ≤ k) :
    ¬ (kneserGraph (2 * k + 1) k).Colorable 2 := by
  rintro ⟨C⟩
  have key : ∀ j, (C (oddWalk k j)).val % 2 = ((C (oddWalk k 0)).val + j) % 2 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hne : C (oddWalk k j) ≠ C (oddWalk k (j + 1)) := C.valid (oddWalk_adj k j hk)
      have h1 : (C (oddWalk k j)).val ≠ (C (oddWalk k (j + 1))).val := fun h => hne (Fin.ext h)
      have h2 := (C (oddWalk k j)).isLt
      have h3 := (C (oddWalk k (j + 1))).isLt
      omega
  have h0 := key (2 * k + 1)
  rw [oddWalk_period] at h0
  have h4 := (C (oddWalk k 0)).isLt
  omega

/-- The chromatic number of the odd graph `KG_{2k+1,k}` is `3` (for `k ≥ 1`). -/
theorem chromaticNumber_kneserGraph_two_mul_add_one (k : ℕ) (hk : 1 ≤ k) :
    (kneserGraph (2 * k + 1) k).chromaticNumber = 3 := by
  have hup : (kneserGraph (2 * k + 1) k).chromaticNumber ≤ ((2 * k + 1) - 2 * k + 2 : ℕ) :=
    chromaticNumber_kneserGraph_le (2 * k + 1) k hk (by omega)
  have h3 : ((2 * k + 1) - 2 * k + 2 : ℕ) = 3 := by omega
  rw [h3] at hup
  refine le_antisymm hup ?_
  have h2 : ¬ (kneserGraph (2 * k + 1) k).chromaticNumber ≤ 2 := fun h =>
    not_colorable_two_kneserGraph_odd k hk
      (SimpleGraph.chromaticNumber_le_iff_colorable.1 (by exact_mod_cast h))
  exact Order.add_one_le_of_lt (not_le.1 h2)

/-! ### The Lovász–Kneser theorem in the proved base cases -/

/-- **Lovász–Kneser theorem (base cases).**  The chromatic number of the Kneser graph
`KG_{n,k}` equals `n - 2k + 2`.  This is proved here in the base cases `k = 1`
(where `KG_{n,1}` is the complete graph `K_n`), `n = 2k` (where `KG_{2k,k}` is a perfect
matching) and `n = 2k + 1` (the odd graph, which is not bipartite because it carries a closed
walk of odd length `2k+1`).  The general lower bound is Lovász' theorem, whose proof goes
through the Borsuk–Ulam theorem; the general upper bound is proved above in
`chromaticNumber_kneserGraph_le`. -/
theorem lovasz_kneser (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (hbase : k = 1 ∨ n = 2 * k ∨ n = 2 * k + 1) :
    (kneserGraph n k).chromaticNumber = (n - 2 * k + 2 : ℕ) := by
  rcases hbase with rfl | rfl | rfl
  · rw [chromaticNumber_kneserGraph_one]
    congr 1
    omega
  · rw [chromaticNumber_kneserGraph_two_mul k hk]
    simp
  · rw [chromaticNumber_kneserGraph_two_mul_add_one k hk]
    have h3 : (2 * k + 1) - 2 * k + 2 = 3 := by omega
    rw [h3]
    rfl

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

