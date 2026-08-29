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

/-! ## The Kneser graph -/

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of an `n`-element set,
and two of them are adjacent when they are disjoint. -/
def kneserGraph (n k : ℕ) : SimpleGraph (KneserVertex n k) where
  Adj s t := s ≠ t ∧ Disjoint (s : Finset (Fin n)) (t : Finset (Fin n))
  symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp] lemma kneserGraph_adj {n k : ℕ} {s t : KneserVertex n k} :
    (kneserGraph n k).Adj s t ↔
      s ≠ t ∧ Disjoint (s : Finset (Fin n)) (t : Finset (Fin n)) := Iff.rfl

/-! ## Counting elements of `Fin n` above or below a threshold -/

/-- The number of elements of `Fin n` whose value is at least `L`. -/
lemma card_filter_le_val (n L : ℕ) :
    (Finset.univ.filter (fun y : Fin n => L ≤ (y : ℕ))).card = n - L := by
  have himg : (Finset.univ.filter (fun y : Fin n => L ≤ (y : ℕ))).image Fin.val
      = Finset.Ico L n := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.isLt⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h2⟩, h1, rfl⟩
  rw [← Finset.card_image_of_injective _ Fin.val_injective, himg, Nat.card_Ico]

/-- The number of elements of `Fin n` whose value is less than `L ≤ n`. -/
lemma card_filter_val_lt (n L : ℕ) (h : L ≤ n) :
    (Finset.univ.filter (fun y : Fin n => (y : ℕ) < L)).card = L := by
  have himg : (Finset.univ.filter (fun y : Fin n => (y : ℕ) < L)).image Fin.val
      = Finset.range L := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, lt_of_lt_of_le hx h⟩, hx, rfl⟩
  rw [← Finset.card_image_of_injective _ Fin.val_injective, himg, Finset.card_range]

/-! ## The upper bound `χ(KG_{n,k}) ≤ n - 2k + 2` -/

/-- The standard colouring bound: the Kneser graph `KG_{n,k}` is `(n - 2k + 2)`-colourable.

A `k`-set `S` is coloured by `min (min S) (n - 2k + 1)`.  Two disjoint sets cannot share a
colour `< n - 2k + 1` since then they would share their smallest element, and they cannot both
get the colour `n - 2k + 1` since then they would both be contained in the last `2k - 1`
elements. -/
lemma kneser_colorable (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (kneserGraph n k).Colorable (n - 2 * k + 2) := by
  classical
  have hne : ∀ S : KneserVertex n k, (S : Finset (Fin n)).Nonempty := by
    intro S
    rw [← Finset.card_pos, S.2]
    omega
  refine ⟨SimpleGraph.Coloring.mk
    (fun S => (⟨min ((S.1.min' (hne S)) : ℕ) (n - 2 * k + 1), by omega⟩ :
      Fin (n - 2 * k + 2))) ?_⟩
  intro S T hadj hcol
  obtain ⟨-, hdisj⟩ := hadj
  set L := n - 2 * k + 1 with hLdef
  have hcol' : min ((S.1.min' (hne S)) : ℕ) L = min ((T.1.min' (hne T)) : ℕ) L := by
    simpa using congrArg Fin.val hcol
  rcases lt_or_ge ((S.1.min' (hne S)) : ℕ) L with h | h
  · have heq : ((S.1.min' (hne S)) : ℕ) = ((T.1.min' (hne T)) : ℕ) := by omega
    have hfin : S.1.min' (hne S) = T.1.min' (hne T) := Fin.val_injective heq
    have h1 : S.1.min' (hne S) ∈ S.1 := Finset.min'_mem _ _
    have h2 : S.1.min' (hne S) ∈ T.1 := hfin ▸ Finset.min'_mem _ _
    exact (Finset.disjoint_left.mp hdisj h1) h2
  · have h' : L ≤ ((T.1.min' (hne T)) : ℕ) := by omega
    have hsub : S.1 ∪ T.1 ⊆ Finset.univ.filter (fun y : Fin n => L ≤ (y : ℕ)) := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Finset.mem_union.mp hy with hy | hy
      · exact le_trans h (Fin.le_def.mp (Finset.min'_le _ _ hy))
      · exact le_trans h' (Fin.le_def.mp (Finset.min'_le _ _ hy))
    have hcard : (S.1 ∪ T.1).card = 2 * k := by
      rw [Finset.card_union_of_disjoint hdisj, S.2, T.2]; ring
    have hle := Finset.card_le_card hsub
    rw [hcard, card_filter_le_val] at hle
    omega

/-! ## The base case `k = 1`: the complete graph -/

/-- Lower bound in the base case `k = 1`: `KG_{n,1}` is the complete graph on `n` vertices. -/
lemma kneser_one_chromaticNumber_ge (n : ℕ) :
    (n : ℕ∞) ≤ (kneserGraph n 1).chromaticNumber := by
  refine SimpleGraph.le_chromaticNumber_of_pairwise_adj (ι := Fin n) (by simp)
    (fun i => ⟨{i}, Finset.card_singleton i⟩) ?_
  intro i j hij
  have h1 : ({i} : Finset (Fin n)) ≠ {j} := by simp [hij]
  exact ⟨fun h => h1 (congrArg Subtype.val h), Finset.disjoint_singleton.mpr hij⟩

/-- The base case `k = 1`: the Kneser graph `KG_{n,1}` is the complete graph `K_n`, so its
chromatic number is `n`. -/
theorem kneser_one_chromaticNumber (n : ℕ) (hn : 2 ≤ n) :
    (kneserGraph n 1).chromaticNumber = (n : ℕ∞) := by
  refine le_antisymm ?_ (kneser_one_chromaticNumber_ge n)
  have h := kneser_colorable n 1 le_rfl hn
  have he : n - 2 * 1 + 2 = n := by omega
  rw [he] at h
  exact h.chromaticNumber_le

/-! ## The odd Kneser graph `KG_{2k+1,k}` -/

section Odd

variable (k : ℕ)

/-- The cyclic arc `{i, i+1, …, i+k-1}` (indices mod `2k+1`) inside `Fin (2k+1)`. -/
def arc (i : ℕ) : Finset (Fin (2 * k + 1)) :=
  (Finset.range k).image
    (fun t => (⟨(i + t) % (2 * k + 1), Nat.mod_lt _ (by omega)⟩ : Fin (2 * k + 1)))

lemma mem_arc {i : ℕ} {x : Fin (2 * k + 1)} :
    x ∈ arc k i ↔ ∃ t < k, (x : ℕ) = (i + t) % (2 * k + 1) := by
  simp only [arc, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, hx⟩
    exact ⟨t, ht, Fin.ext hx.symm⟩

lemma arc_card (i : ℕ) : (arc k i).card = k := by
  rw [arc, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  have h1 : (i + a) % (2 * k + 1) = (i + b) % (2 * k + 1) := congrArg Fin.val hab
  have h2 : a % (2 * k + 1) = b % (2 * k + 1) := Nat.ModEq.add_left_cancel' i h1
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2

lemma arc_disjoint (i : ℕ) : Disjoint (arc k i) (arc k (i + k)) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [mem_arc] at hx hx'
  obtain ⟨t, ht, hxt⟩ := hx
  obtain ⟨s, hs, hxs⟩ := hx'
  have h1 : (i + t) % (2 * k + 1) = (i + (k + s)) % (2 * k + 1) := by
    rw [← hxt, hxs]; ring_nf
  have h2 : t % (2 * k + 1) = (k + s) % (2 * k + 1) := Nat.ModEq.add_left_cancel' i h1
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
  omega

lemma arc_period (i : ℕ) : arc k (i + (2 * k + 1) * k) = arc k i := by
  have haux : ∀ t : ℕ, (i + (2 * k + 1) * k + t) % (2 * k + 1) = (i + t) % (2 * k + 1) := by
    intro t
    rw [show i + (2 * k + 1) * k + t = (i + t) + (2 * k + 1) * k by ring,
      Nat.add_mul_mod_self_left]
  ext x
  simp only [mem_arc]
  constructor
  · rintro ⟨t, ht, hx⟩
    exact ⟨t, ht, by rw [hx, haux]⟩
  · rintro ⟨t, ht, hx⟩
    exact ⟨t, ht, by rw [hx, haux]⟩

/-- The arc `arc k i` viewed as a vertex of `KG_{2k+1,k}`. -/
def arcVertex (i : ℕ) : KneserVertex (2 * k + 1) k := ⟨arc k i, arc_card k i⟩

lemma arcVertex_adj (hk : 1 ≤ k) (i : ℕ) :
    (kneserGraph (2 * k + 1) k).Adj (arcVertex k (i + k)) (arcVertex k i) := by
  have hd : Disjoint (arc k i) (arc k (i + k)) := arc_disjoint k i
  have hnonempty : (arc k i).Nonempty := by
    rw [← Finset.card_pos, arc_card]
    omega
  obtain ⟨x, hx⟩ := hnonempty
  refine ⟨fun h => ?_, hd.symm⟩
  have h' : arc k (i + k) = arc k i := congrArg Subtype.val h
  exact (Finset.disjoint_left.mp hd hx) (h' ▸ hx)

/-- `KG_{2k+1,k}` is not `2`-colourable: the arcs `arc k (m * k)`, `m = 0, …, 2k`, form a
cycle of odd length `2k + 1`. -/
lemma kneser_odd_not_colorable_two (hk : 1 ≤ k) :
    ¬ (kneserGraph (2 * k + 1) k).Colorable 2 := by
  rintro ⟨C⟩
  have hfin : ∀ x y z : Fin 2, x ≠ y → (x = z ↔ ¬ (y = z)) := by decide
  have key : ∀ m : ℕ, (C (arcVertex k (m * k)) = C (arcVertex k 0)) ↔ Even m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show (m + 1) * k = m * k + k by ring,
        hfin _ _ _ (C.valid (arcVertex_adj k hk (m * k))), ih, Nat.even_add_one]
  have hper : arcVertex k ((2 * k + 1) * k) = arcVertex k 0 := by
    have h := arc_period k 0
    simp only [Nat.zero_add] at h
    exact Subtype.ext h
  have h2 := (key (2 * k + 1)).mp (by rw [hper])
  simp [parity_simps] at h2

/-- The odd Kneser graph: `χ(KG_{2k+1,k}) = 3` for `k ≥ 1`. -/
theorem kneser_odd_chromaticNumber (hk : 1 ≤ k) :
    (kneserGraph (2 * k + 1) k).chromaticNumber = 3 := by
  have hcol : (kneserGraph (2 * k + 1) k).Colorable 3 := by
    have h := kneser_colorable (2 * k + 1) k hk (by omega)
    have he : 2 * k + 1 - 2 * k + 2 = 3 := by omega
    rwa [he] at h
  have h3 : ((2 : ℕ) : ℕ∞) + 1 = 3 := by norm_num
  rw [← h3, SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable]
  exact ⟨hcol, kneser_odd_not_colorable_two k hk⟩

end Odd

/-! ## The case `n = 2k`: a perfect matching -/

/-- The case `n = 2k`: `KG_{2k,k}` is a perfect matching, so `χ = 2`. -/
theorem kneser_double_chromaticNumber (k : ℕ) (hk : 1 ≤ k) :
    (kneserGraph (2 * k) k).chromaticNumber = 2 := by
  classical
  have hcol : (kneserGraph (2 * k) k).Colorable 2 := by
    have h := kneser_colorable (2 * k) k hk le_rfl
    have he : 2 * k - 2 * k + 2 = 2 := by omega
    rwa [he] at h
  refine le_antisymm hcol.chromaticNumber_le ?_
  have hlow : ((2 : ℕ) : ℕ∞) ≤ (kneserGraph (2 * k) k).chromaticNumber := by
    have hlt : (Finset.univ.filter (fun y : Fin (2 * k) => (y : ℕ) < k)).card = k :=
      card_filter_val_lt _ _ (by omega)
    have hge : (Finset.univ.filter (fun y : Fin (2 * k) => k ≤ (y : ℕ))).card = k := by
      rw [card_filter_le_val]
      omega
    set S : KneserVertex (2 * k) k :=
      ⟨Finset.univ.filter (fun y : Fin (2 * k) => (y : ℕ) < k), hlt⟩ with hS
    set T : KneserVertex (2 * k) k :=
      ⟨Finset.univ.filter (fun y : Fin (2 * k) => k ≤ (y : ℕ)), hge⟩ with hT
    have hdisj : Disjoint (S : Finset (Fin (2 * k))) (T : Finset (Fin (2 * k))) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [hS, hT, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
      omega
    have hSne : S ≠ T := by
      intro h
      have hnonempty : (S : Finset (Fin (2 * k))).Nonempty := by
        rw [← Finset.card_pos, hlt]
        omega
      obtain ⟨x, hx⟩ := hnonempty
      exact (Finset.disjoint_left.mp hdisj hx) (h ▸ hx)
    refine SimpleGraph.le_chromaticNumber_of_pairwise_adj (ι := Fin 2) (by simp)
      (fun i => if i = 0 then S else T) ?_
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hSne, hdisj, hdisj.symm, Ne.symm hSne]
  exact_mod_cast hlow

/-! ## The main statement -/

/-- **Lovász–Kneser theorem (base cases).**

The chromatic number of the Kneser graph `KG_{n,k}` equals `n - 2k + 2`.  This is established
here in the base cases `k = 1` (where `KG_{n,1}` is the complete graph `K_n`) and `n ≤ 2k + 1`
(where `KG_{2k,k}` is a perfect matching and `KG_{2k+1,k}` is the odd Kneser graph, of
chromatic number `3`).  The upper bound `χ(KG_{n,k}) ≤ n - 2k + 2` is proved in full generality
in `Frontier.kneser_colorable`.  The general lower bound is Lovász's theorem, whose known
proofs go through the Borsuk–Ulam theorem (or Tucker's lemma), which is not currently
available in Mathlib. -/
theorem lovasz_kneser (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (hcase : k = 1 ∨ n ≤ 2 * k + 1) :
    (kneserGraph n k).chromaticNumber = ((n - 2 * k + 2 : ℕ) : ℕ∞) := by
  rcases hcase with rfl | hle
  · rw [kneser_one_chromaticNumber n (by omega)]
    congr 1
    omega
  · rcases (by omega : n = 2 * k ∨ n = 2 * k + 1) with rfl | rfl
    · rw [kneser_double_chromaticNumber k hk]
      norm_num
    · rw [kneser_odd_chromaticNumber k hk]
      norm_num

end Frontier

