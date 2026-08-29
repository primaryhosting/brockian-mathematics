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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of an `n`-element set,
and two of them are adjacent when they are disjoint. -/
def kneserGraph (n k : ℕ) : SimpleGraph (KneserVertex n k) where
  Adj s t := (s : Finset (Fin n)) ≠ (t : Finset (Fin n)) ∧
      Disjoint (s : Finset (Fin n)) (t : Finset (Fin n))
  symm := by
    rintro s t ⟨h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma kneserGraph_adj {n k : ℕ} (s t : KneserVertex n k) :
    (kneserGraph n k).Adj s t ↔
      (s : Finset (Fin n)) ≠ (t : Finset (Fin n)) ∧
        Disjoint (s : Finset (Fin n)) (t : Finset (Fin n)) := Iff.rfl

/-- The standard colouring gives the upper bound `χ(KG_{n,k}) ≤ n - 2k + 2`. -/
theorem kneser_colorable (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (kneserGraph n k).Colorable (n - 2 * k + 2) := by
  have hne : ∀ v : KneserVertex n k, (v : Finset (Fin n)).Nonempty := by
    intro v
    exact Finset.card_pos.mp (by rw [v.2]; omega)
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => (⟨min ((((v : Finset (Fin n)).min' (hne v)) : Fin n) : ℕ) (n - 2 * k + 1),
      by omega⟩ : Fin (n - 2 * k + 2))) ?_⟩
  rintro v w ⟨-, hd⟩ hcolor
  set a : ℕ := ((((v : Finset (Fin n)).min' (hne v)) : Fin n) : ℕ) with ha
  set b : ℕ := ((((w : Finset (Fin n)).min' (hne w)) : Fin n) : ℕ) with hb
  have key : min a (n - 2 * k + 1) = min b (n - 2 * k + 1) := by
    have := congrArg Fin.val hcolor
    simpa using this
  by_cases hlt : a < n - 2 * k + 1
  · -- the two sets share their minimum
    have hba : b = a := by omega
    have hmin : (w : Finset (Fin n)).min' (hne w) = (v : Finset (Fin n)).min' (hne v) :=
      Fin.val_injective hba
    have h1 : (v : Finset (Fin n)).min' (hne v) ∈ (v : Finset (Fin n)) := Finset.min'_mem _ _
    have h2 : (v : Finset (Fin n)).min' (hne v) ∈ (w : Finset (Fin n)) := by
      rw [← hmin]; exact Finset.min'_mem _ _
    exact (Finset.disjoint_left.mp hd h1) h2
  · -- both sets live in the last `2k - 1` points, so they cannot be disjoint
    have hMa : n - 2 * k + 1 ≤ a := by omega
    have hMb : n - 2 * k + 1 ≤ b := by omega
    have hsub : ((v : Finset (Fin n)) ∪ (w : Finset (Fin n))).image Fin.val ⊆
        Finset.Ico (n - 2 * k + 1) n := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_union] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      refine Finset.mem_Ico.mpr ⟨?_, i.isLt⟩
      rcases hi with hi | hi
      · have : a ≤ (i : ℕ) := Fin.le_def.mp (Finset.min'_le _ i hi)
        omega
      · have : b ≤ (i : ℕ) := Fin.le_def.mp (Finset.min'_le _ i hi)
        omega
    have hcard : ((v : Finset (Fin n)) ∪ (w : Finset (Fin n))).card = 2 * k := by
      rw [Finset.card_union_of_disjoint hd, v.2, w.2]; ring
    have h1 : (((v : Finset (Fin n)) ∪ (w : Finset (Fin n))).image Fin.val).card = 2 * k := by
      rw [Finset.card_image_of_injective _ Fin.val_injective, hcard]
    have h2 := Finset.card_le_card hsub
    rw [h1, Nat.card_Ico] at h2
    omega

/-- `KG_{n,1}` is the complete graph on the `1`-element subsets of `Fin n`. -/
theorem kneserGraph_one (n : ℕ) : kneserGraph n 1 = (⊤ : SimpleGraph (KneserVertex n 1)) := by
  ext s t
  simp only [kneserGraph_adj, SimpleGraph.top_adj]
  constructor
  · rintro ⟨h1, -⟩
    exact fun h => h1 (congrArg Subtype.val h)
  · intro h
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp s.2
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp t.2
    have hne : a ≠ b := by
      rintro rfl
      exact h (Subtype.ext (ha.trans hb.symm))
    rw [ha, hb]
    exact ⟨by simpa using hne, by simpa using hne⟩

/-- Chromatic number of `KG_{n,1}` (the complete graph `K_n`). -/
theorem kneser_chromaticNumber_one (n : ℕ) :
    (kneserGraph n 1).chromaticNumber = (n : ℕ∞) := by
  rw [kneserGraph_one, SimpleGraph.chromaticNumber_top]
  congr 1
  simp

/-- Chromatic number of `KG_{2k,k}` (a perfect matching), for `k ≥ 1`. -/
theorem kneser_chromaticNumber_two_mul (k : ℕ) (hk : 1 ≤ k) :
    (kneserGraph (2 * k) k).chromaticNumber = 2 := by
  have h2k : 0 < 2 * k := by omega
  -- Upper bound: colour a `k`-set by whether it contains the point `0`.
  have hcol : (kneserGraph (2 * k) k).Colorable 2 := by
    refine ⟨SimpleGraph.Coloring.mk
      (fun v => if (⟨0, h2k⟩ : Fin (2 * k)) ∈ (v : Finset (Fin (2 * k))) then (0 : Fin 2) else 1)
      ?_⟩
    rintro v w ⟨-, hd⟩
    have hcard : ((v : Finset (Fin (2 * k))) ∪ (w : Finset (Fin (2 * k)))).card = 2 * k := by
      rw [Finset.card_union_of_disjoint hd, v.2, w.2]; ring
    have huniv : (v : Finset (Fin (2 * k))) ∪ (w : Finset (Fin (2 * k))) = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa using hcard)
    have hmem : (⟨0, h2k⟩ : Fin (2 * k)) ∈
        (v : Finset (Fin (2 * k))) ∪ (w : Finset (Fin (2 * k))) := by
      rw [huniv]; exact Finset.mem_univ _
    rw [Finset.mem_union] at hmem
    rcases hmem with h | h
    · have h' : (⟨0, h2k⟩ : Fin (2 * k)) ∉ (w : Finset (Fin (2 * k))) :=
        fun hw => (Finset.disjoint_left.mp hd h) hw
      simp [h, h']
    · have h' : (⟨0, h2k⟩ : Fin (2 * k)) ∉ (v : Finset (Fin (2 * k))) :=
        fun hv => (Finset.disjoint_left.mp hd hv) h
      simp [h, h']
  -- Lower bound: the graph contains an edge.
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin (2 * k)))) (n := k) (by simp; omega)
  have hsc : (sᶜ).card = k := by
    rw [Finset.card_compl, hs]; simp; omega
  obtain ⟨a, ha⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
  have hne : s ≠ sᶜ := by
    intro hcon
    exact (Finset.mem_compl.mp (hcon ▸ ha)) ha
  have hadj : (kneserGraph (2 * k) k).Adj ⟨s, hs⟩ ⟨sᶜ, hsc⟩ := ⟨hne, disjoint_compl_right⟩
  have hvw : (⟨s, hs⟩ : KneserVertex (2 * k) k) ≠ ⟨sᶜ, hsc⟩ :=
    fun h => hne (congrArg Subtype.val h)
  have hclique : (kneserGraph (2 * k) k).IsClique
      (↑({⟨s, hs⟩, ⟨sᶜ, hsc⟩} : Finset (KneserVertex (2 * k) k))) := by
    simp only [Finset.coe_insert, Finset.coe_singleton]
    exact SimpleGraph.isClique_pair.mpr (fun _ => hadj)
  have hlow := hclique.card_le_chromaticNumber
  rw [Finset.card_insert_of_notMem (by simpa using hvw), Finset.card_singleton] at hlow
  refine le_antisymm ?_ (by exact_mod_cast hlow)
  exact_mod_cast SimpleGraph.chromaticNumber_le_iff_colorable.mpr hcol

/-! ### The odd graphs `KG_{2k+1,k}`

These contain an odd cycle, given by the cyclically consecutive blocks of `k` residues,
which forces the chromatic number to be at least `3`. -/

/-- The residue of `m` modulo `2k+1`, as an element of `Fin (2k+1)`. -/
def cycRes (k m : ℕ) : Fin (2 * k + 1) := ⟨m % (2 * k + 1), Nat.mod_lt _ (by omega)⟩

/-- The block of `k` cyclically consecutive residues `m, m+1, …, m+k-1` modulo `2k+1`. -/
def cycBlock (k m : ℕ) : Finset (Fin (2 * k + 1)) :=
  (Finset.range k).image (fun j => cycRes k (m + j))

lemma cycRes_eq_iff (k a b : ℕ) :
    cycRes k a = cycRes k b ↔ a % (2 * k + 1) = b % (2 * k + 1) := by
  constructor
  · intro h; exact congrArg Fin.val h
  · intro h; exact Fin.ext h

lemma cycBlock_congr (k a b : ℕ) (h : a % (2 * k + 1) = b % (2 * k + 1)) :
    cycBlock k a = cycBlock k b := by
  unfold cycBlock
  refine Finset.image_congr ?_
  intro j _
  refine (cycRes_eq_iff k _ _).mpr ?_
  simpa [Nat.add_mod] using congrArg (fun t => (t + j % (2 * k + 1)) % (2 * k + 1)) h

lemma cycBlock_card (k m : ℕ) : (cycBlock k m).card = k := by
  have hinj : Set.InjOn (fun j => cycRes k (m + j)) (Finset.range k) := by
    intro x hx y hy hxy
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    have h1 : (m + x) % (2 * k + 1) = (m + y) % (2 * k + 1) :=
      (cycRes_eq_iff k _ _).mp hxy
    have h2 : x % (2 * k + 1) = y % (2 * k + 1) := Nat.ModEq.add_left_cancel' m h1
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
  rw [cycBlock, Finset.card_image_of_injOn hinj, Finset.card_range]

lemma cycBlock_disjoint (k m : ℕ) (hk : 1 ≤ k) :
    Disjoint (cycBlock k m) (cycBlock k (m + k)) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [cycBlock, Finset.mem_image, Finset.mem_range] at hx hx'
  obtain ⟨a, ha, hae⟩ := hx
  obtain ⟨b, hb, hbe⟩ := hx'
  have h1 : (m + (k + b)) % (2 * k + 1) = (m + a) % (2 * k + 1) := by
    have := (cycRes_eq_iff k (m + k + b) (m + a)).mp (hbe.trans hae.symm)
    rwa [Nat.add_assoc] at this
  have h2 : (k + b) % (2 * k + 1) = a % (2 * k + 1) := Nat.ModEq.add_left_cancel' m h1
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
  omega

lemma cycBlock_ne (k m : ℕ) (hk : 1 ≤ k) : cycBlock k m ≠ cycBlock k (m + k) := by
  intro hcon
  have hdis : Disjoint (cycBlock k m) (cycBlock k m) := by
    nth_rewrite 2 [hcon]
    exact cycBlock_disjoint k m hk
  have hempty : cycBlock k m = ∅ := disjoint_self.mp hdis
  have := cycBlock_card k m
  rw [hempty] at this
  simp at this
  omega

/-- The vertex of `KG_{2k+1,k}` given by the cyclic block starting at `m`. -/
def cycVertex (k m : ℕ) : KneserVertex (2 * k + 1) k :=
  ⟨cycBlock k m, cycBlock_card k m⟩

lemma cycVertex_adj (k m : ℕ) (hk : 1 ≤ k) :
    (kneserGraph (2 * k + 1) k).Adj (cycVertex k m) (cycVertex k (m + k)) :=
  ⟨cycBlock_ne k m hk, cycBlock_disjoint k m hk⟩

lemma cycVertex_congr (k a b : ℕ) (h : a % (2 * k + 1) = b % (2 * k + 1)) :
    cycVertex k a = cycVertex k b :=
  Subtype.ext (cycBlock_congr k a b h)

/-- The odd graph `KG_{2k+1,k}` is not `2`-colourable: the cyclic blocks form an odd cycle. -/
theorem kneser_not_colorable_two (k : ℕ) (hk : 1 ≤ k) :
    ¬ (kneserGraph (2 * k + 1) k).Colorable 2 := by
  rintro ⟨C⟩
  have hstep : ∀ m : ℕ, C (cycVertex k (m * k)) ≠ C (cycVertex k ((m + 1) * k)) := by
    intro m
    have hcong : cycVertex k (m * k + k) = cycVertex k ((m + 1) * k) :=
      cycVertex_congr k _ _ (by ring_nf)
    have := C.valid (cycVertex_adj k (m * k) hk)
    rwa [hcong] at this
  have key : ∀ m : ℕ, (C (cycVertex k (m * k)) = C (cycVertex k 0)) ↔ m % 2 = 0 := by
    intro m
    induction m with
    | zero => simp
    | succ p ih =>
      have hflip : ∀ x y z : Fin 2, x ≠ y → ((y = z) ↔ ¬ (x = z)) := by decide
      have h1 := hflip _ _ (C (cycVertex k 0)) (hstep p)
      rw [h1, ih]
      omega
  have hzero : cycVertex k ((2 * k + 1) * k) = cycVertex k 0 :=
    cycVertex_congr k _ _ (by simp [Nat.mul_mod_right])
  have hcontra := (key (2 * k + 1)).mp (by rw [hzero])
  omega

/-- Chromatic number of the odd graph `KG_{2k+1,k}`, for `k ≥ 1`. -/
theorem kneser_chromaticNumber_two_mul_add_one (k : ℕ) (hk : 1 ≤ k) :
    (kneserGraph (2 * k + 1) k).chromaticNumber = 3 := by
  have hupper : (kneserGraph (2 * k + 1) k).Colorable 3 := by
    have := kneser_colorable (2 * k + 1) k hk (by omega)
    have heq : 2 * k + 1 - 2 * k + 2 = 3 := by omega
    rwa [heq] at this
  have hle : (kneserGraph (2 * k + 1) k).chromaticNumber ≤ 3 := by
    exact_mod_cast SimpleGraph.chromaticNumber_le_iff_colorable.mpr hupper
  have hnot : ¬ ((kneserGraph (2 * k + 1) k).chromaticNumber ≤ 2) := by
    intro hcon
    exact kneser_not_colorable_two k hk
      (SimpleGraph.chromaticNumber_le_iff_colorable.mp (by exact_mod_cast hcon))
  have hge : (3 : ℕ∞) ≤ (kneserGraph (2 * k + 1) k).chromaticNumber := by
    have h2 : (2 : ℕ∞) < (kneserGraph (2 * k + 1) k).chromaticNumber := not_le.mp hnot
    have := Order.add_one_le_of_lt h2
    norm_num at this
    exact this
  exact le_antisymm hle hge

/-- **Lovász–Kneser theorem**, base cases.
The chromatic number of the Kneser graph `KG_{n,k}` equals `n - 2k + 2`,
proved here in the base cases `k = 1` (the complete graph `K_n`), `n = 2k`
(a perfect matching) and `n = 2k + 1` (the odd graphs). -/
theorem lovasz_kneser (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (hbase : k = 1 ∨ n = 2 * k ∨ n = 2 * k + 1) :
    (kneserGraph n k).chromaticNumber = ((n - 2 * k + 2 : ℕ) : ℕ∞) := by
  rcases hbase with rfl | rfl | rfl
  · rw [kneser_chromaticNumber_one]
    congr 1
    omega
  · rw [kneser_chromaticNumber_two_mul k hk]
    simp
  · rw [kneser_chromaticNumber_two_mul_add_one k hk]
    have heq : 2 * k + 1 - 2 * k + 2 = 3 := by omega
    rw [heq]
    rfl

end Frontier

