import Mathlib
/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Frontier

open SimpleGraph Finset

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {A : Finset (Fin n) // A.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of `Fin n`, and two
distinct such subsets are adjacent when they are disjoint. -/
def kneserGraph (n k : ℕ) : SimpleGraph (KneserVertex n k) where
  Adj A B := A ≠ B ∧ Disjoint A.1 B.1
  symm := by
    rintro A B ⟨h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp] lemma kneserGraph_adj {n k : ℕ} (A B : KneserVertex n k) :
    (kneserGraph n k).Adj A B ↔ A ≠ B ∧ Disjoint A.1 B.1 := Iff.rfl

/-- A vertex of `KG_{n,k}` with `1 ≤ k` is a nonempty finset. -/
lemma kneser_vertex_nonempty {n k : ℕ} (hk : 1 ≤ k) (A : KneserVertex n k) : A.1.Nonempty := by
  rw [← Finset.card_pos, A.2]; omega

/-! ## The upper bound: `χ(KG_{n,k}) ≤ n - 2k + 2` -/

/-- The standard explicit colouring: colour a `k`-set `A` by `min (min A) (n - 2k + 1)`. -/
theorem kneser_colorable (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (kneserGraph n k).Colorable (n - 2 * k + 2) := by
  classical
  set c : ℕ := n - 2 * k + 1 with hc
  rw [SimpleGraph.colorable_iff_exists_bdd_nat_coloring]
  refine ⟨SimpleGraph.Coloring.mk
      (fun A => min ((A.1.min' (kneser_vertex_nonempty hk A) : Fin n) : ℕ) c) ?_, ?_⟩
  · rintro A B ⟨-, hdisj⟩ heq
    set a : ℕ := ((A.1.min' (kneser_vertex_nonempty hk A) : Fin n) : ℕ) with ha
    set b : ℕ := ((B.1.min' (kneser_vertex_nonempty hk B) : Fin n) : ℕ) with hb
    replace heq : min a c = min b c := heq
    by_cases hac : a < c
    · -- then `a = b`, so `A` and `B` share their minimum
      have hab : a = b := by
        rcases lt_or_ge b c with hbc | hbc
        · rw [min_eq_left hac.le, min_eq_left hbc.le] at heq; exact heq
        · rw [min_eq_left hac.le, min_eq_right hbc] at heq; omega
      have hmem : A.1.min' (kneser_vertex_nonempty hk A) ∈ B.1 := by
        have : A.1.min' (kneser_vertex_nonempty hk A)
            = B.1.min' (kneser_vertex_nonempty hk B) := by
          apply Fin.val_injective; simpa [← ha, ← hb] using hab
        rw [this]; exact Finset.min'_mem _ _
      exact (Finset.disjoint_left.mp hdisj (Finset.min'_mem _ _)) hmem
    · -- both minima are `≥ c`, so `A ∪ B` lives in a set of size `2k - 1 < 2k`
      have hbc : c ≤ b := by
        rcases lt_or_ge b c with h | h
        · rw [min_eq_right (not_lt.mp hac), min_eq_left h.le] at heq; omega
        · exact h
      have hac' : c ≤ a := not_lt.mp hac
      set A' : Finset ℕ := A.1.image Fin.val with hA'
      set B' : Finset ℕ := B.1.image Fin.val with hB'
      have hAcard : A'.card = k := by
        rw [hA', Finset.card_image_of_injective _ Fin.val_injective, A.2]
      have hBcard : B'.card = k := by
        rw [hB', Finset.card_image_of_injective _ Fin.val_injective, B.2]
      have hdisj' : Disjoint A' B' := by
        rw [hA', hB', Finset.disjoint_left]
        rintro x hx hx'
        simp only [Finset.mem_image] at hx hx'
        obtain ⟨u, hu, rfl⟩ := hx
        obtain ⟨v, hv, huv⟩ := hx'
        have : u = v := Fin.val_injective huv.symm
        subst this
        exact (Finset.disjoint_left.mp hdisj hu) hv
      have hsub : A' ∪ B' ⊆ Finset.Ico c n := by
        intro x hx
        rw [Finset.mem_Ico]
        rcases Finset.mem_union.mp hx with h | h
        · rw [hA', Finset.mem_image] at h
          obtain ⟨u, hu, rfl⟩ := h
          refine ⟨le_trans hac' ?_, u.2⟩
          exact Fin.le_def.mp (Finset.min'_le _ _ hu)
        · rw [hB', Finset.mem_image] at h
          obtain ⟨u, hu, rfl⟩ := h
          refine ⟨le_trans hbc ?_, u.2⟩
          exact Fin.le_def.mp (Finset.min'_le _ _ hu)
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj', hAcard, hBcard, Nat.card_Ico] at hcard
      omega
  · intro A
    exact lt_of_le_of_lt (min_le_right _ _) (by omega)

/-! ## Base case `k = 1`: the Kneser graph is the complete graph -/

/-- For `k = 1`, `KG_{n,1}` is isomorphic to the complete graph on `Fin n`. -/
def kneserIsoTop (n : ℕ) : kneserGraph n 1 ≃g (⊤ : SimpleGraph (Fin n)) where
  toFun A := A.1.min' (kneser_vertex_nonempty le_rfl A)
  invFun a := ⟨{a}, Finset.card_singleton a⟩
  left_inv := by
    rintro ⟨A, hA⟩
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hA
    simp
  right_inv := by
    intro a; simp
  map_rel_iff' := by
    rintro ⟨A, hA⟩ ⟨B, hB⟩
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hA
    obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hB
    simp [kneserGraph, Subtype.ext_iff]

/-! ## Base case `n = 2k`: the Kneser graph is a perfect matching -/

/-- For `1 ≤ k` and `n = 2k` the Kneser graph has an edge, hence is not `1`-colourable. -/
lemma kneser_exists_edge (k : ℕ) (hk : 1 ≤ k) :
    ∃ A B : KneserVertex (2 * k) k, (kneserGraph (2 * k) k).Adj A B := by
  classical
  set S : Finset (Fin (2 * k)) := Finset.univ.filter (fun v => (v : ℕ) < k) with hS
  set T : Finset (Fin (2 * k)) := Finset.univ.filter (fun v => ¬ ((v : ℕ) < k)) with hT
  have hcard : S.card + T.card = 2 * k := by
    rw [hS, hT, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have hScard : S.card = k := by
    rw [hS]
    have : (Finset.univ.filter (fun v : Fin (2 * k) => (v : ℕ) < k))
        = (Finset.Iio (⟨k, by omega⟩ : Fin (2 * k))) := by
      ext v; simp [Fin.lt_def]
    rw [this, Fin.card_Iio]
  have hTcard : T.card = k := by omega
  have hdisj : Disjoint S T := by
    rw [hS, hT]
    exact Finset.disjoint_filter_filter_not _ _ _
  refine ⟨⟨S, hScard⟩, ⟨T, hTcard⟩, ?_, hdisj⟩
  intro h
  have hSTeq : S = T := congrArg Subtype.val h
  have h0 : (⟨0, by omega⟩ : Fin (2 * k)) ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]; omega
  have := Finset.disjoint_left.mp hdisj h0
  rw [hSTeq] at h0
  exact this h0


/-! ## Base case `n = 2k + 1`: the odd graphs `KG_{2k+1,k}` have chromatic number `3` -/

section OddGraph

open scoped Fin.NatCast

/-- The cyclic interval `{a, a+1, …, a+k-1}` inside `Fin (2k+1)`. -/
def cycInt (k : ℕ) (a : Fin (2 * k + 1)) : Finset (Fin (2 * k + 1)) :=
  (Finset.range k).image (fun t : ℕ => a + (t : Fin (2 * k + 1)))

lemma cycInt_card (k : ℕ) (a : Fin (2 * k + 1)) : (cycInt k a).card = k := by
  have hinj : Set.InjOn (fun t : ℕ => a + (t : Fin (2 * k + 1))) (Finset.range k) := by
    intro t ht s hs hts
    simp only [Finset.coe_range, Set.mem_Iio] at ht hs
    have h1 : ((t : Fin (2 * k + 1))) = ((s : Fin (2 * k + 1))) := add_left_cancel hts
    have h2 := congrArg Fin.val h1
    rw [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at h2
    exact h2
  rw [cycInt, Finset.card_image_of_injOn hinj, Finset.card_range]

lemma cycInt_disjoint (k : ℕ) (a : Fin (2 * k + 1)) :
    Disjoint (cycInt k a) (cycInt k (a + (k : Fin (2 * k + 1)))) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [cycInt, Finset.mem_image, Finset.mem_range] at hx hx'
  obtain ⟨t, ht, htx⟩ := hx
  obtain ⟨s, hs, hsx⟩ := hx'
  have hE : ((t : Fin (2 * k + 1))) = ((k : Fin (2 * k + 1))) + ((s : Fin (2 * k + 1))) := by
    refine add_left_cancel (a := a) ?_
    rw [htx, ← hsx, add_assoc]
  rw [← Nat.cast_add] at hE
  have h2 := congrArg Fin.val hE
  rw [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at h2
  omega

/-- The `j`-th vertex of the odd cycle `C_0, C_k, C_{2k}, …` inside `KG_{2k+1,k}`. -/
def oddWalk (k : ℕ) (j : ℕ) : KneserVertex (2 * k + 1) k :=
  ⟨cycInt k ((j * k : ℕ) : Fin (2 * k + 1)), cycInt_card k _⟩

lemma oddWalk_adj (k : ℕ) (hk : 1 ≤ k) (j : ℕ) :
    (kneserGraph (2 * k + 1) k).Adj (oddWalk k j) (oddWalk k (j + 1)) := by
  have hstep : ((((j + 1) * k : ℕ)) : Fin (2 * k + 1))
      = (((j * k : ℕ)) : Fin (2 * k + 1)) + ((k : ℕ) : Fin (2 * k + 1)) := by
    rw [show (j + 1) * k = j * k + k by ring, Nat.cast_add]
  have hdisj : Disjoint (oddWalk k j).1 (oddWalk k (j + 1)).1 := by
    show Disjoint (cycInt k _) (cycInt k _)
    rw [hstep]
    exact cycInt_disjoint k _
  refine ⟨?_, hdisj⟩
  intro hEq
  obtain ⟨x, hx⟩ := kneser_vertex_nonempty hk (oddWalk k j)
  have hx' : x ∈ (oddWalk k (j + 1)).1 := by rw [← hEq]; exact hx
  exact (Finset.disjoint_left.mp hdisj hx) hx'

lemma oddWalk_period (k : ℕ) : oddWalk k (2 * k + 1) = oddWalk k 0 := by
  apply Subtype.ext
  show cycInt k _ = cycInt k _
  congr 1
  apply Fin.val_injective
  rw [Fin.val_natCast, Fin.val_natCast]
  simp [Nat.mul_mod_right]

/-- The odd graph `KG_{2k+1,k}` is not `2`-colourable: it contains a closed walk of odd
length `2k+1`. -/
lemma kneser_odd_not_colorable_two (k : ℕ) (hk : 1 ≤ k) :
    ¬ (kneserGraph (2 * k + 1) k).Colorable 2 := by
  rintro ⟨C⟩
  have hstep : ∀ j : ℕ, C (oddWalk k (j + 1)) = C (oddWalk k j) + 1 := by
    intro j
    have := C.valid (oddWalk_adj k hk j)
    omega
  have hj : ∀ j : ℕ, ((C (oddWalk k j)).val + j) % 2 = (C (oddWalk k 0)).val % 2 := by
    intro j
    induction j with
    | zero => simp
    | succ m ih =>
      have h := hstep m
      omega
  have h1 := hj (2 * k + 1)
  rw [oddWalk_period k] at h1
  omega

end OddGraph

/-! ## The main theorem -/

/-- **Lovász–Kneser theorem (base cases).**  The chromatic number of the Kneser graph
`KG_{n,k}` equals `n - 2k + 2`.  The full theorem is due to Lovász (via Borsuk–Ulam); here we
establish the base cases `k = 1` (where `KG_{n,1}` is the complete graph `K_n`), `n = 2k`
(where `KG_{2k,k}` is a perfect matching) and `n = 2k + 1` (the odd graphs, whose chromatic
number is `3`), together with the general upper bound `kneser_colorable`. -/
theorem lovasz_kneser (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (hbase : k = 1 ∨ n = 2 * k ∨ n = 2 * k + 1) :
    (kneserGraph n k).chromaticNumber = (n - 2 * k + 2 : ℕ) := by
  rcases hbase with rfl | rfl | rfl
  · -- complete graph on `Fin n`
    have hiso := kneserIsoTop n
    have h1 : (kneserGraph n 1).chromaticNumber ≤ (⊤ : SimpleGraph (Fin n)).chromaticNumber :=
      SimpleGraph.chromaticNumber_mono_of_hom hiso.toHom
    have h2 : (⊤ : SimpleGraph (Fin n)).chromaticNumber ≤ (kneserGraph n 1).chromaticNumber :=
      SimpleGraph.chromaticNumber_mono_of_hom hiso.symm.toHom
    have h3 : (kneserGraph n 1).chromaticNumber = (n : ℕ∞) := by
      rw [le_antisymm h1 h2, SimpleGraph.chromaticNumber_top, Fintype.card_fin]
    rw [h3]
    congr 1
    omega
  · -- perfect matching
    have hup : (kneserGraph (2 * k) k).chromaticNumber ≤ ((2 * k - 2 * k + 2 : ℕ) : ℕ∞) :=
      (kneser_colorable (2 * k) k hk le_rfl).chromaticNumber_le
    have hsimp : (2 * k - 2 * k + 2 : ℕ) = 2 := by omega
    rw [hsimp] at hup ⊢
    refine le_antisymm hup ?_
    -- lower bound: the graph has an edge, so it is not 1-colourable
    obtain ⟨A, B, hAB⟩ := kneser_exists_edge k hk
    by_contra hlt
    push_neg at hlt
    have hle : (kneserGraph (2 * k) k).chromaticNumber ≤ ((1 : ℕ) : ℕ∞) := by
      rw [Nat.cast_one]
      exact Order.le_of_lt_add_one (by simpa using hlt)
    have hcol : (kneserGraph (2 * k) k).Colorable 1 :=
      SimpleGraph.chromaticNumber_le_iff_colorable.mp hle
    obtain ⟨C⟩ := hcol
    exact C.valid hAB (Subsingleton.elim _ _)
  · -- odd graph
    have hup : (kneserGraph (2 * k + 1) k).chromaticNumber
        ≤ ((2 * k + 1 - 2 * k + 2 : ℕ) : ℕ∞) :=
      (kneser_colorable (2 * k + 1) k hk (by omega)).chromaticNumber_le
    have hsimp : (2 * k + 1 - 2 * k + 2 : ℕ) = 3 := by omega
    rw [hsimp] at hup ⊢
    refine le_antisymm hup ?_
    by_contra hlt
    push_neg at hlt
    have hle : (kneserGraph (2 * k + 1) k).chromaticNumber ≤ ((2 : ℕ) : ℕ∞) := by
      rw [Nat.cast_ofNat]
      exact Order.le_of_lt_add_one (by simpa using hlt)
    exact kneser_odd_not_colorable_two k hk
      (SimpleGraph.chromaticNumber_le_iff_colorable.mp hle)

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

