import Mathlib

/-!
# Abstract machinery for paradoxical decompositions

This file develops the general theory needed for the Banach–Tarski paradox, on top of
Mathlib's `Equidecomp` (equidecompositions for a group action).
-/

open Set Function Pointwise

namespace BT

variable {X G H : Type*} [Nonempty X] [Group G] [MulAction G X]

/-- Build an equidecomposition out of a function which is a bijection from `A` to `B` and
moves every point of `A` by an element of a fixed finite set of group elements. -/
noncomputable def mkEquidecomp (f : X → X) (A B : Set X) (S : Finset G)
    (hd : Equidecomp.IsDecompOn f A S) (hb : BijOn f A B) : Equidecomp X G where
  toPartialEquiv := hb.toPartialEquiv f A B
  isDecompOn' := ⟨S, hd⟩

@[simp] lemma mkEquidecomp_source (f : X → X) (A B : Set X) (S : Finset G)
    (hd : Equidecomp.IsDecompOn f A S) (hb : BijOn f A B) :
    (mkEquidecomp f A B S hd hb).source = A := rfl

@[simp] lemma mkEquidecomp_target (f : X → X) (A B : Set X) (S : Finset G)
    (hd : Equidecomp.IsDecompOn f A S) (hb : BijOn f A B) :
    (mkEquidecomp f A B S hd hb).target = B := rfl

/-- `A` is `G`-paradoxical: it contains two disjoint subsets, each of which is
equidecomposable (using the group `G`) with all of `A`. -/
def Paradoxical (G : Type*) [Group G] [MulAction G X] (A : Set X) : Prop :=
  ∃ f g : Equidecomp X G, f.source ⊆ A ∧ g.source ⊆ A ∧ Disjoint f.source g.source ∧
    f.target = A ∧ g.target = A

omit [Nonempty X] in
lemma eq_trans_source (a b : Equidecomp X G) :
    (a.trans b).source = a.source ∩ (a.toPartialEquiv) ⁻¹' b.source := rfl

omit [Nonempty X] in
lemma eq_trans_target (a b : Equidecomp X G) :
    (a.trans b).target = b.target ∩ (b.toPartialEquiv.symm) ⁻¹' a.target := rfl

omit [Nonempty X] in
lemma eq_symm_source (a : Equidecomp X G) : a.symm.source = a.target := rfl

omit [Nonempty X] in
lemma eq_symm_target (a : Equidecomp X G) : a.symm.target = a.source := rfl

omit [Nonempty X] in
/-- Paradoxicality transfers along an equidecomposition. -/
theorem Paradoxical.of_equidecomp {A A' : Set X} (e : Equidecomp X G)
    (hs : e.source = A') (ht : e.target = A) (h : Paradoxical G A) : Paradoxical G A' := by
  obtain ⟨f, g, hfs, hgs, hd, hft, hgt⟩ := h
  have key : ∀ k : Equidecomp X G, k.source ⊆ A → k.target = A →
      (e.trans (k.trans e.symm)).source = A' ∩ (e.toPartialEquiv) ⁻¹' k.source ∧
      (e.trans (k.trans e.symm)).target = A' := by
    intro k hks hkt
    have h1 : (k.trans e.symm).source = k.source := by
      rw [eq_trans_source, eq_symm_source, ht]
      refine inter_eq_left.mpr fun x hx => ?_
      rw [mem_preimage, ← hkt]
      exact k.toPartialEquiv.map_source hx
    have h2 : (k.trans e.symm).target = A' := by
      rw [eq_trans_target, eq_symm_target, hs, hkt]
      refine inter_eq_left.mpr fun x hx => ?_
      show e.toPartialEquiv x ∈ A
      rw [← ht]
      exact e.toPartialEquiv.map_source (hs ▸ hx)
    refine ⟨?_, ?_⟩
    · rw [eq_trans_source, h1, hs]
    · rw [eq_trans_target, h2, ht]
      refine inter_eq_left.mpr fun x hx => ?_
      have hx' : x ∈ (k.trans e.symm).target := by rw [h2]; exact hx
      have h3 := (k.trans e.symm).toPartialEquiv.map_target hx'
      rw [h1] at h3
      exact hks h3
  obtain ⟨hf1, hf2⟩ := key f hfs hft
  obtain ⟨hg1, hg2⟩ := key g hgs hgt
  refine ⟨e.trans (f.trans e.symm), e.trans (g.trans e.symm), by rw [hf1]; exact inter_subset_left,
    by rw [hg1]; exact inter_subset_left, ?_, hf2, hg2⟩
  rw [hf1, hg1]
  exact Disjoint.inter_left' _ (Disjoint.inter_right' _ (hd.preimage _))

omit [Nonempty X] in
/-- Paradoxicality transfers along a group homomorphism compatible with the actions. -/
theorem Paradoxical.map {H : Type*} [Group H] [MulAction H X] (ψ : G →* H)
    (hψ : ∀ (g : G) (x : X), (ψ g) • x = g • x) {A : Set X} (h : Paradoxical G A) :
    Paradoxical H A := by
  classical
  obtain ⟨f, g, hfs, hgs, hd, hft, hgt⟩ := h
  have conv : ∀ k : Equidecomp X G, ∃ k' : Equidecomp X H,
      k'.toPartialEquiv = k.toPartialEquiv := by
    intro k
    refine ⟨⟨k.toPartialEquiv, k.witness.image ψ, ?_⟩, rfl⟩
    intro a ha
    obtain ⟨c, hc, hca⟩ := k.isDecompOn a ha
    exact ⟨ψ c, Finset.mem_image_of_mem _ hc, by rw [hψ]; exact hca⟩
  obtain ⟨f', hf'⟩ := conv f
  obtain ⟨g', hg'⟩ := conv g
  have hfs' : f'.source = f.source := congrArg PartialEquiv.source hf'
  have hgs' : g'.source = g.source := congrArg PartialEquiv.source hg'
  have hft' : f'.target = f.target := congrArg PartialEquiv.target hf'
  have hgt' : g'.target = g.target := congrArg PartialEquiv.target hg'
  exact ⟨f', g', hfs' ▸ hfs, hgs' ▸ hgs, hfs' ▸ hgs' ▸ hd, hft' ▸ hft, hgt' ▸ hgt⟩

/-- **Absorption lemma.** If some `ρ : G` pushes `D` into `A` along all its powers,
keeping the positive powers off `D`, then `A \ D` is equidecomposable with `A`. -/
theorem exists_equidecomp_sdiff {A D : Set X} (ρ : G)
    (hsub : ∀ n : ℕ, (ρ ^ n) • D ⊆ A)
    (hdisj : ∀ n : ℕ, 1 ≤ n → Disjoint ((ρ ^ n) • D) D) :
    ∃ e : Equidecomp X G, e.source = A \ D ∧ e.target = A := by
  classical
  set U : Set X := ⋃ n : ℕ, (ρ ^ n) • D with hUdef
  set U' : Set X := ⋃ n : ℕ, (ρ ^ (n + 1)) • D with hU'def
  have hUA : U ⊆ A := iUnion_subset hsub
  have hU'U : U' ⊆ U := iUnion_subset fun n => subset_iUnion_of_subset (n + 1) (le_refl _)
  have hU'D : ∀ x ∈ U', x ∉ D := by
    intro x hx hxD
    rw [hU'def, mem_iUnion] at hx
    obtain ⟨n, hn⟩ := hx
    exact (hdisj (n + 1) (Nat.succ_le_succ (Nat.zero_le n))).notMem_of_mem_left hn hxD
  have hUsplit : ∀ x, x ∈ U → x ∈ D ∨ x ∈ U' := by
    intro x hx
    rw [hUdef, mem_iUnion] at hx
    obtain ⟨n, hn⟩ := hx
    cases n with
    | zero => left; simpa using hn
    | succ m => right; exact mem_iUnion.2 ⟨m, hn⟩
  have hinvU' : ρ⁻¹ • U' = U := by
    rw [hU'def, hUdef, Set.smul_set_iUnion]
    refine iUnion_congr fun n => ?_
    rw [smul_smul, pow_succ', inv_mul_cancel_left]
  refine ⟨mkEquidecomp (fun x => if x ∈ U' then ρ⁻¹ • x else x) (A \ D) A {1, ρ⁻¹} ?_ ?_, rfl, rfl⟩
  · intro a _
    by_cases h : a ∈ U'
    · exact ⟨ρ⁻¹, by simp, by simp [h]⟩
    · exact ⟨1, by simp, by simp [h]⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      by_cases h : x ∈ U'
      · simp only [h, if_true]
        exact hUA (hinvU' ▸ smul_mem_smul_set h)
      · simpa [h] using hx.1
    · intro x hx y hy hxy
      by_cases hx' : x ∈ U' <;> by_cases hy' : y ∈ U' <;>
        simp only [hx', hy', if_true, if_false] at hxy
      · exact MulAction.injective ρ⁻¹ hxy
      · exact absurd (hinvU' ▸ smul_mem_smul_set hx' : ρ⁻¹ • x ∈ U)
          (hxy ▸ fun hc => hy.2 (Or.resolve_right (hUsplit y hc) hy'))
      · exact absurd (hinvU' ▸ smul_mem_smul_set hy' : ρ⁻¹ • y ∈ U)
          (hxy ▸ fun hc => hx.2 (Or.resolve_right (hUsplit x hc) hx'))
      · exact hxy
    · intro y hy
      by_cases h : y ∈ U
      · have hy' : ρ • y ∈ U' := by
          have h2 : ρ • y ∈ ρ • U := smul_mem_smul_set h
          rwa [← hinvU', smul_smul, mul_inv_cancel, one_smul] at h2
        refine ⟨ρ • y, ⟨hUA (hU'U hy'), hU'D _ hy'⟩, ?_⟩
        simp [hy', smul_smul]
      · refine ⟨y, ⟨hy, fun hc => h (subset_iUnion_of_subset 0 (by simp) hc)⟩, ?_⟩
        have hy' : y ∉ U' := fun hc => h (hU'U hc)
        simp [hy']

/-! ### Words starting with a given letter -/

open FreeGroup in
/-- Multiplying a word which does not start with `i` by `i⁻¹` yields a word starting with
`i⁻¹`. -/
lemma inv_mul_mem_startsWith {i : Fin 2} {g : FreeGroup (Fin 2)}
    (hg : g ∉ startsWith (i, true)) : (FreeGroup.of i)⁻¹ * g ∈ startsWith (i, false) := by
  have h := FreeGroup.startsWith_mk_mul (w := (i, false)) g (by simpa using hg)
  simpa [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev] using h

open FreeGroup in
/-- Multiplying a word starting with `i⁻¹` by `i` never yields a word starting with `i`. -/
lemma mul_notMem_startsWith {i : Fin 2} {h : FreeGroup (Fin 2)}
    (hh : h ∈ startsWith (i, false)) : FreeGroup.of i * h ∉ startsWith (i, true) := by
  have hw : h.toWord = (i, false) :: h.toWord.tail := by
    unfold FreeGroup.startsWith at hh
    simp only [Set.mem_setOf_eq] at hh
    match hl : h.toWord with
    | [] => simp [hl] at hh
    | x :: t => simp [hl] at hh; simp [hh]
  have hred : FreeGroup.IsReduced h.toWord := FreeGroup.isReduced_toWord
  have key : (FreeGroup.of i * h).toWord = h.toWord.tail := by
    rw [FreeGroup.toWord_mul, show (FreeGroup.of i).toWord = [(i, true)] from FreeGroup.toWord_of i,
      hw]
    simp only [List.cons_append, List.nil_append]
    rw [FreeGroup.reduce.cons,
      show FreeGroup.reduce ((i, false) :: h.toWord.tail) = (i, false) :: h.toWord.tail from
        (hw ▸ hred).reduce_eq]
    simp
  intro hc
  unfold FreeGroup.startsWith at hc
  simp only [Set.mem_setOf_eq, key] at hc
  match hl : h.toWord.tail with
  | [] => simp [hl] at hc
  | y :: t =>
      rw [hl] at hc
      simp at hc
      have hred' : FreeGroup.IsReduced ((i, false) :: y :: t) := by rw [← hl, ← hw]; exact hred
      have h2 := (FreeGroup.isReduced_cons_cons.mp hred').1
      rw [hc] at h2
      simp at h2

/-- A set on which a free group of rank two acts freely is paradoxical. -/
theorem paradoxical_of_free (φ : FreeGroup (Fin 2) →* G) (A : Set X)
    (hinv : ∀ w : FreeGroup (Fin 2), (φ w) • A ⊆ A)
    (hfree : ∀ x ∈ A, ∀ w : FreeGroup (Fin 2), (φ w) • x = x → w = 1) :
    Paradoxical G A := by
  classical
  have hmem : ∀ (w : FreeGroup (Fin 2)) (x : X), x ∈ A → φ w • x ∈ A :=
    fun w x hx => hinv w ⟨x, hx, rfl⟩
  let s : Setoid X := ⟨fun x y => ∃ w : FreeGroup (Fin 2), φ w • x = y,
    ⟨fun x => ⟨1, by simp⟩,
     fun ⟨w, hw⟩ => ⟨w⁻¹, by rw [← hw, ← mul_smul, ← map_mul]; simp⟩,
     fun ⟨w, hw⟩ ⟨v, hv⟩ => ⟨v * w, by rw [map_mul, mul_smul, hw, hv]⟩⟩⟩
  set rep : X → X := fun x => (Quotient.mk s x).out with hrepdef
  have hrep : ∀ x : X, ∃ w : FreeGroup (Fin 2), φ w • rep x = x :=
    fun x => Quotient.mk_out (s := s) x
  have hrep_eq : ∀ x y : X, (∃ w : FreeGroup (Fin 2), φ w • x = y) → rep x = rep y := by
    intro x y h
    have hq : Quotient.mk s x = Quotient.mk s y := Quotient.sound h
    rw [hrepdef]; simp only [hq]
  set ω : X → FreeGroup (Fin 2) := fun x => (hrep x).choose with hωdef
  have hω : ∀ x, φ (ω x) • rep x = x := fun x => (hrep x).choose_spec
  have hrepA : ∀ x ∈ A, rep x ∈ A := by
    intro x hx
    have h1 : φ ((ω x)⁻¹) • x = rep x := by
      rw [map_inv, inv_smul_eq_iff]; exact (hω x).symm
    rw [← h1]
    exact hmem _ _ hx
  have huniq : ∀ x ∈ A, ∀ w, φ w • rep x = x → w = ω x := by
    intro x hx w hw
    have h1 : φ ((ω x)⁻¹ * w) • rep x = rep x := by
      rw [map_mul, mul_smul, hw, map_inv, inv_smul_eq_iff]
      exact (hω x).symm
    exact (inv_mul_eq_one.mp (hfree _ (hrepA x hx) _ h1)).symm
  have hequiv : ∀ x ∈ A, ∀ u : FreeGroup (Fin 2), ω (φ u • x) = u * ω x := by
    intro x hx u
    have h1 : rep (φ u • x) = rep x := (hrep_eq x (φ u • x) ⟨u, rfl⟩).symm
    refine (huniq _ (hmem u x hx) (u * ω x) ?_).symm
    rw [h1, map_mul, mul_smul, hω x]
  -- the four pieces
  set S : Fin 2 × Bool → Set X := fun v => {x | x ∈ A ∧ ω x ∈ FreeGroup.startsWith v} with hSdef
  have hSA : ∀ v, S v ⊆ A := fun v x hx => hx.1
  have main : ∀ i : Fin 2, ∃ f : Equidecomp X G,
      f.source = S (i, true) ∪ S (i, false) ∧ f.target = A := by
    intro i
    set a : FreeGroup (Fin 2) := FreeGroup.of i with hadef
    have hne : ∀ g : FreeGroup (Fin 2), g ∈ FreeGroup.startsWith (i, false) →
        g ∉ FreeGroup.startsWith (i, true) := by
      intro g hg hg'
      exact (FreeGroup.startsWith.disjoint_iff_ne.mpr (by simp)).notMem_of_mem_left hg hg'
    refine ⟨mkEquidecomp
      (fun x => if ω x ∈ FreeGroup.startsWith (i, false) then φ a • x else x)
      (S (i, true) ∪ S (i, false)) A {1, φ a} ?_ ?_, rfl, rfl⟩
    · intro x _
      by_cases h : ω x ∈ FreeGroup.startsWith (i, false)
      · exact ⟨φ a, by simp, by simp [h]⟩
      · exact ⟨1, by simp, by simp [h]⟩
    · have hsrcA : S (i, true) ∪ S (i, false) ⊆ A := union_subset (hSA _) (hSA _)
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        by_cases h : ω x ∈ FreeGroup.startsWith (i, false)
        · simpa [h] using hmem a x (hsrcA hx)
        · simpa [h] using hsrcA hx
      · intro x hx y hy hxy
        by_cases hx' : ω x ∈ FreeGroup.startsWith (i, false) <;>
          by_cases hy' : ω y ∈ FreeGroup.startsWith (i, false) <;>
          simp only [hx', hy', if_true, if_false] at hxy
        · exact MulAction.injective (φ a) hxy
        · exfalso
          have hyt : ω y ∈ FreeGroup.startsWith (i, true) :=
            (hy.resolve_right (fun hc => hy' hc.2)).2
          have : ω y = a * ω x := by rw [← hxy]; exact hequiv x (hsrcA hx) a
          exact mul_notMem_startsWith hx' (this ▸ hyt)
        · exfalso
          have hxt : ω x ∈ FreeGroup.startsWith (i, true) :=
            (hx.resolve_right (fun hc => hx' hc.2)).2
          have : ω x = a * ω y := by rw [hxy]; exact hequiv y (hsrcA hy) a
          exact mul_notMem_startsWith hy' (this ▸ hxt)
        · exact hxy
      · intro y hy
        by_cases h : ω y ∈ FreeGroup.startsWith (i, true)
        · refine ⟨y, Or.inl ⟨hy, h⟩, ?_⟩
          have hnot : ω y ∉ FreeGroup.startsWith (i, false) := fun hc => hne _ hc h
          simp [hnot]
        · refine ⟨φ a⁻¹ • y, Or.inr ⟨hmem _ _ hy, ?_⟩, ?_⟩
          · rw [hequiv y hy a⁻¹]
            exact inv_mul_mem_startsWith h
          · have hmem' : ω (φ a⁻¹ • y) ∈ FreeGroup.startsWith (i, false) := by
              rw [hequiv y hy a⁻¹]; exact inv_mul_mem_startsWith h
            simp only [hmem', if_true]
            rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  obtain ⟨f, hf1, hf2⟩ := main 0
  obtain ⟨g, hg1, hg2⟩ := main 1
  refine ⟨f, g, by rw [hf1]; exact union_subset (hSA _) (hSA _),
    by rw [hg1]; exact union_subset (hSA _) (hSA _), ?_, hf2, hg2⟩
  rw [hf1, hg1]
  simp only [Set.disjoint_left, mem_union]
  rintro x (hx | hx) (hy | hy) <;>
    exact (FreeGroup.startsWith.disjoint_iff_ne.mpr (by simp)).notMem_of_mem_left hx.2 hy.2

end BT

import RequestProject.Abstract
import RequestProject.Space

/-!
# Radial extension

A paradoxical decomposition of a subset of the unit sphere extends radially to a paradoxical
decomposition of the corresponding punctured cone in the unit ball.
-/

open Matrix Set Function

namespace BT

/-- The unit sphere of `ℝ³`. -/
def S2 : Set E := {x : E | ‖x‖ = 1}

/-- The punctured radial cone over a subset of the sphere. -/
def cone (A : Set E) : Set E := {x : E | x ≠ 0 ∧ ‖x‖ ≤ 1 ∧ ‖x‖⁻¹ • x ∈ A}

lemma mem_S2 {x : E} : x ∈ S2 ↔ ‖x‖ = 1 := Iff.rfl

lemma cone_mono {A B : Set E} (h : A ⊆ B) : cone A ⊆ cone B := fun _ hx => ⟨hx.1, hx.2.1, h hx.2.2⟩

lemma norm_normalize {x : E} (hx : x ≠ 0) : ‖‖x‖⁻¹ • x‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

lemma cone_S2 : cone S2 = Metric.closedBall (0 : E) 1 \ {0} := by
  ext x
  constructor
  · rintro ⟨hx0, hx1, -⟩
    exact ⟨by simpa using hx1, hx0⟩
  · rintro ⟨hx1, hx0⟩
    simp only [mem_singleton_iff] at hx0
    exact ⟨hx0, by simpa using hx1, by rw [mem_S2, norm_normalize hx0]⟩

lemma cone_disjoint {A B : Set E} (h : Disjoint A B) : Disjoint (cone A) (cone B) := by
  rw [Set.disjoint_left] at h ⊢
  exact fun x hx hy => h hx.2.2 hy.2.2

/-- Radial extension of an equidecomposition of subsets of the sphere. -/
theorem exists_cone_equidecomp (f : Equidecomp E O3) (hs : f.source ⊆ S2) (ht : f.target ⊆ S2) :
    ∃ g : Equidecomp E O3, g.source = cone f.source ∧ g.target = cone f.target := by
  classical
  set F : E → E := fun x => ‖x‖ • (f.toPartialEquiv (‖x‖⁻¹ • x)) with hF
  have hFval : ∀ x ∈ cone f.source, ‖F x‖ = ‖x‖ ∧ ‖F x‖⁻¹ • F x = f.toPartialEquiv (‖x‖⁻¹ • x) := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1
    have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
    have h1 : ‖f.toPartialEquiv (‖x‖⁻¹ • x)‖ = 1 :=
      ht (f.toPartialEquiv.map_source hx.2.2)
    have h2 : ‖F x‖ = ‖x‖ := by
      rw [hF]
      simp only
      rw [norm_smul, h1, mul_one, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
    refine ⟨h2, ?_⟩
    rw [h2, hF]
    simp only
    rw [smul_smul, inv_mul_cancel₀ hnorm, one_smul]
  refine ⟨mkEquidecomp F (cone f.source) (cone f.target) f.witness ?_ ?_, rfl, rfl⟩
  · intro x hx
    obtain ⟨M, hM, hMx⟩ := f.isDecompOn (‖x‖⁻¹ • x) hx.2.2
    refine ⟨M, hM, ?_⟩
    have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx.1
    show ‖x‖ • (f.toPartialEquiv (‖x‖⁻¹ • x)) = M • x
    rw [show f.toPartialEquiv (‖x‖⁻¹ • x) = M • (‖x‖⁻¹ • x) from hMx, O3.smul_smul_real,
      smul_smul, mul_inv_cancel₀ hnorm, one_smul]
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨h1, h2⟩ := hFval x hx
      refine ⟨?_, ?_, ?_⟩
      · intro hc
        rw [hc, norm_zero] at h1
        exact hx.1 (norm_eq_zero.mp h1.symm)
      · rw [h1]; exact hx.2.1
      · rw [h2]; exact f.toPartialEquiv.map_source hx.2.2
    · intro x hx y hy hxy
      obtain ⟨hx1, hx2⟩ := hFval x hx
      obtain ⟨hy1, hy2⟩ := hFval y hy
      have hnormeq : ‖x‖ = ‖y‖ := by rw [← hx1, ← hy1, hxy]
      have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx.1
      have hval : f.toPartialEquiv (‖x‖⁻¹ • x) = f.toPartialEquiv (‖y‖⁻¹ • y) := by
        rw [← hx2, ← hy2, hxy]
      have hunit : (‖x‖⁻¹ • x) = (‖y‖⁻¹ • y) :=
        f.toPartialEquiv.injOn hx.2.2 hy.2.2 hval
      calc x = ‖x‖ • (‖x‖⁻¹ • x) := by rw [smul_smul, mul_inv_cancel₀ hnorm, one_smul]
        _ = ‖y‖ • (‖y‖⁻¹ • y) := by rw [hunit, hnormeq]
        _ = y := by
            rw [smul_smul, mul_inv_cancel₀ (hnormeq ▸ hnorm), one_smul]
    · intro y hy
      have hy0 : y ≠ 0 := hy.1
      have hnorm : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy0
      set z : E := f.toPartialEquiv.symm (‖y‖⁻¹ • y) with hz
      have hzs : z ∈ f.source := f.toPartialEquiv.map_target hy.2.2
      have hfz : f.toPartialEquiv z = ‖y‖⁻¹ • y := f.toPartialEquiv.right_inv hy.2.2
      have hz1 : ‖z‖ = 1 := hs hzs
      refine ⟨‖y‖ • z, ⟨?_, ?_, ?_⟩, ?_⟩
      · have hzne : z ≠ 0 := by
          intro hc
          rw [hc, norm_zero] at hz1
          exact zero_ne_one hz1
        exact smul_ne_zero hnorm hzne
      · rw [norm_smul, hz1, mul_one, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)]
        exact hy.2.1
      · rw [norm_smul, hz1, mul_one, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y), smul_smul,
          inv_mul_cancel₀ hnorm, one_smul]
        exact hzs
      · show ‖‖y‖ • z‖ • (f.toPartialEquiv (‖‖y‖ • z‖⁻¹ • (‖y‖ • z))) = y
        rw [norm_smul, hz1, mul_one, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y), smul_smul,
          inv_mul_cancel₀ hnorm, one_smul, hfz, smul_smul, mul_inv_cancel₀ hnorm, one_smul]

/-- Radial extension of a paradoxical decomposition. -/
theorem paradoxical_cone {A : Set E} (h : Paradoxical O3 A) (hA : A ⊆ S2) :
    Paradoxical O3 (cone A) := by
  obtain ⟨f, g, hfs, hgs, hd, hft, hgt⟩ := h
  obtain ⟨f', hf1, hf2⟩ := exists_cone_equidecomp f (hfs.trans hA) (by rw [hft]; exact hA)
  obtain ⟨g', hg1, hg2⟩ := exists_cone_equidecomp g (hgs.trans hA) (by rw [hgt]; exact hA)
  refine ⟨f', g', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf1]; exact cone_mono hfs
  · rw [hg1]; exact cone_mono hgs
  · rw [hf1, hg1]; exact cone_disjoint hd
  · rw [hf2, hft]
  · rw [hg2, hgt]

end BT

import Mathlib

/-!
# Euclidean 3-space, the orthogonal group and the isometry group

Basic set-up used throughout the Banach–Tarski development: the space `E = ℝ³`,
the action of the orthogonal group `O3` of `3 × 3` matrices on it, the group `Isom`
of isometries of `E`, and the homomorphism `O3 →* Isom`.
-/

open Matrix Set Function

namespace BT

/-- Euclidean 3-space. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-- The group of orthogonal `3 × 3` real matrices. -/
abbrev O3 := Matrix.orthogonalGroup (Fin 3) ℝ

noncomputable instance : SMul O3 E where
  smul M x := WithLp.toLp 2 ((M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ WithLp.ofLp x)

lemma O3.smul_apply (M : O3) (x : E) (i : Fin 3) :
    (M • x) i = ∑ j, (M : Matrix (Fin 3) (Fin 3) ℝ) i j * x j := rfl

lemma O3.smul_eq (M : O3) (x : E) :
    M • x = WithLp.toLp 2 ((M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ WithLp.ofLp x) := rfl

lemma O3.mem_iff (M : O3) : (M : Matrix (Fin 3) (Fin 3) ℝ) * (M : Matrix (Fin 3) (Fin 3) ℝ)ᵀ = 1 :=
  (Matrix.mem_orthogonalGroup_iff _ _).1 M.2

lemma O3.transpose_mul (M : O3) :
    (M : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * (M : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  have := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).1 M.2
  simpa using this

noncomputable instance : MulAction O3 E where
  one_smul x := by
    ext i; simp
  mul_smul M N x := by
    ext i
    simp only [O3.smul_apply, Submonoid.coe_mul]
    simp [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm

lemma O3.coe_inv (M : O3) :
    ((M⁻¹ : O3) : Matrix (Fin 3) (Fin 3) ℝ) = (M : Matrix (Fin 3) (Fin 3) ℝ)ᵀ := by
  have h : ((M⁻¹ : O3) : Matrix (Fin 3) (Fin 3) ℝ) = star (M : Matrix (Fin 3) (Fin 3) ℝ) := rfl
  rw [h]
  ext i j
  simp [Matrix.star_apply]

lemma O3.smul_sub (M : O3) (x y : E) : M • (x - y) = M • x - M • y := by
  ext i
  simp only [O3.smul_apply, PiLp.sub_apply, mul_sub]
  exact Finset.sum_sub_distrib (f := fun j => (M : Matrix (Fin 3) (Fin 3) ℝ) i j * x j)
    (g := fun j => (M : Matrix (Fin 3) (Fin 3) ℝ) i j * y j)

/-- Orthogonal matrices preserve the Euclidean norm. -/
lemma O3.norm_smul (M : O3) (x : E) : ‖M • x‖ = ‖x‖ := by
  set a : Matrix (Fin 3) (Fin 3) ℝ := (M : Matrix (Fin 3) (Fin 3) ℝ) with ha
  have h : ∀ j k : Fin 3, ∑ i, a i j * a i k = if j = k then 1 else 0 := by
    intro j k
    have := congrFun (congrFun (O3.transpose_mul M) j) k
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply] using this
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [O3.smul_apply, Real.norm_eq_abs, sq_abs]
  have h1 : ∀ i : Fin 3, (∑ j, a i j * x j) ^ 2 = ∑ j, ∑ k, (a i j * a i k) * (x j * x k) := by
    intro i
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm]
  have h2 : ∀ j : Fin 3, ∑ i, ∑ k, (a i j * a i k) * (x j * x k) = (x j) ^ 2 := by
    intro j
    rw [Finset.sum_comm]
    have h3 : ∀ k : Fin 3,
        ∑ i, (a i j * a i k) * (x j * x k) = (if j = k then 1 else 0) * (x j * x k) := by
      intro k; rw [← h j k, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun k _ => h3 k]
    simp [Finset.sum_ite_eq]
    ring
  rw [Finset.sum_congr rfl fun j _ => h2 j]

lemma O3.smul_smul_real (M : O3) (r : ℝ) (x : E) : M • (r • x) = r • (M • x) := by
  ext i
  simp only [O3.smul_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma O3.smul_zero' (M : O3) : M • (0 : E) = 0 := by
  ext i; simp

/-- The group of isometries of Euclidean 3-space. -/
abbrev Isom := E ≃ᵢ E

instance : MulAction Isom E where
  smul f x := f x
  one_smul _ := rfl
  mul_smul f g x := IsometryEquiv.mul_apply f g x

lemma Isom.smul_def (f : Isom) (x : E) : f • x = f x := rfl

/-- An orthogonal matrix, viewed as an isometry of `E`. -/
noncomputable def O3.toIsomFun (M : O3) : E ≃ᵢ E where
  toEquiv :=
    { toFun := fun x => M • x
      invFun := fun x => M⁻¹ • x
      left_inv := fun x => by
        show M⁻¹ • (M • x) = x
        rw [← SemigroupAction.mul_smul, inv_mul_cancel, one_smul]
      right_inv := fun x => by
        show M • (M⁻¹ • x) = x
        rw [← SemigroupAction.mul_smul, mul_inv_cancel, one_smul] }
  isometry_toFun := by
    refine Isometry.of_dist_eq fun x y => ?_
    simp only [dist_eq_norm, ← O3.smul_sub, O3.norm_smul]

@[simp] lemma O3.toIsomFun_apply (M : O3) (x : E) : O3.toIsomFun M x = M • x := rfl

/-- The orthogonal group as a subgroup of the isometry group. -/
noncomputable def O3.toIsom : O3 →* Isom where
  toFun := O3.toIsomFun
  map_one' := by
    refine IsometryEquiv.ext fun x => ?_
    show (1 : O3) • x = x
    exact one_smul _ x
  map_mul' M N := by
    refine IsometryEquiv.ext fun x => ?_
    show (M * N) • x = M • (N • x)
    exact SemigroupAction.mul_smul M N x

lemma O3.toIsom_smul (M : O3) (x : E) : (O3.toIsom M) • x = M • x := rfl

end BT

import RequestProject.Space

/-!
# Fixed points of a rotation

A nontrivial rotation of `ℝ³` (an orthogonal matrix of determinant one) fixes only the two
points where its axis meets the unit sphere. In particular its fixed points on the sphere
form a countable (indeed, finite) set.
-/

open Matrix Set Function

namespace BT

lemma cross_mulVec (M : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ) :
    Mᵀ *ᵥ (crossProduct (M *ᵥ u) (M *ᵥ v)) = M.det • crossProduct u v := by
  funext i
  fin_cases i <;>
    simp [cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.det_fin_three] <;>
    ring

/-- Two vectors with vanishing cross product are parallel. -/
lemma exists_smul_of_cross_eq_zero {u v : Fin 3 → ℝ} (hu : u ≠ 0) (h : crossProduct u v = 0) :
    ∃ c : ℝ, v = c • u := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [cross_apply] at h0 h1 h2
  have hex : ∃ i, u i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hu (funext hc)
  obtain ⟨i, hi⟩ := hex
  have main : ∀ i : Fin 3, u i ≠ 0 → ∃ c : ℝ, v = c • u := by
    intro i hi
    refine ⟨v i / u i, ?_⟩
    funext j
    have key : u i * v j = v i * u j := by
      match i, j with
      | 0, 0 => ring
      | 0, 1 => linarith
      | 0, 2 => linarith
      | 1, 0 => linarith
      | 1, 1 => ring
      | 1, 2 => linarith
      | 2, 0 => linarith
      | 2, 1 => linarith
      | 2, 2 => ring
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linarith
  exact main i hi

/-- A rotation which fixes two vectors with nonzero cross product is the identity: the cross
product is fixed as well, giving an invertible fixed frame. -/
theorem eq_one_of_fixed_indep (M : Matrix (Fin 3) (Fin 3) ℝ) (horth : M * Mᵀ = 1)
    (hdet : M.det = 1) {u v : Fin 3 → ℝ} (hu : M *ᵥ u = u) (hv : M *ᵥ v = v)
    (hw0 : crossProduct u v ≠ 0) : M = 1 := by
  set w := crossProduct u v with hwdef
  have hMw : M *ᵥ w = w := by
    have h1 := cross_mulVec M u v
    rw [hu, hv, hdet, one_smul] at h1
    calc M *ᵥ w = M *ᵥ (Mᵀ *ᵥ w) := by rw [h1]
      _ = (M * Mᵀ) *ᵥ w := by rw [Matrix.mulVec_mulVec]
      _ = w := by rw [horth, Matrix.one_mulVec]
  set N : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (fun i j => ![u, v, w] j i) with hN
  have hdetN : N.det ≠ 0 := by
    have hval : N.det = w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 := by
      simp only [hN, Matrix.det_fin_three, hwdef, cross_apply]
      simp [Matrix.of_apply]
      ring
    rw [hval]
    intro hzero
    refine hw0 (funext fun k => ?_)
    fin_cases k <;>
      simp <;> nlinarith [sq_nonneg (w 0), sq_nonneg (w 1), sq_nonneg (w 2)]
  have hcols : ∀ j : Fin 3, M *ᵥ (![u, v, w] j) = ![u, v, w] j := by
    intro j
    fin_cases j
    · exact hu
    · exact hv
    · exact hMw
  have hMN : M * N = N := by
    ext i j
    have h1 : (M * N) i j = (M *ᵥ (![u, v, w] j)) i := rfl
    rw [h1, hcols j]
    rfl
  have hunit : IsUnit N.det := isUnit_iff_ne_zero.mpr hdetN
  calc M = M * (N * N⁻¹) := by rw [Matrix.mul_nonsing_inv _ hunit, mul_one]
    _ = M * N * N⁻¹ := by rw [mul_assoc]
    _ = N * N⁻¹ := by rw [hMN]
    _ = 1 := Matrix.mul_nonsing_inv _ hunit

/-- Two vectors fixed by a nontrivial rotation are parallel. -/
theorem fixed_parallel (M : Matrix (Fin 3) (Fin 3) ℝ) (horth : M * Mᵀ = 1) (hdet : M.det = 1)
    (hne : M ≠ 1) {u v : Fin 3 → ℝ} (hu : M *ᵥ u = u) (hv : M *ᵥ v = v) (hu0 : u ≠ 0) :
    ∃ c : ℝ, v = c • u := by
  by_cases hc : crossProduct u v = 0
  · exact exists_smul_of_cross_eq_zero hu0 hc
  · exact absurd (eq_one_of_fixed_indep M horth hdet hu hv hc) hne

/-- The unit vectors fixed by a nontrivial rotation form a countable set. -/
theorem countable_fixed (M : O3) (hdet : (M : Matrix (Fin 3) (Fin 3) ℝ).det = 1) (hne : M ≠ 1) :
    {x : E | ‖x‖ = 1 ∧ M • x = x}.Countable := by
  rcases eq_empty_or_nonempty {x : E | ‖x‖ = 1 ∧ M • x = x} with h | ⟨x0, hx0⟩
  · rw [h]; exact countable_empty
  · have hMne : (M : Matrix (Fin 3) (Fin 3) ℝ) ≠ 1 := fun hc => hne (Subtype.ext hc)
    have hfix : ∀ x : E, M • x = x → (M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (fun i => x i) =
        (fun i => x i) := by
      intro x hx
      funext i
      have := congrArg (fun y : E => y i) hx
      simpa [O3.smul_apply, Matrix.mulVec, dotProduct] using this
    have hx0' := hfix x0 hx0.2
    have hx00 : (fun i => x0 i) ≠ (0 : Fin 3 → ℝ) := by
      intro hc
      have : ‖x0‖ = 0 := by
        rw [EuclideanSpace.norm_eq]
        have : ∀ i, x0 i = 0 := fun i => congrFun hc i
        simp [this]
      rw [hx0.1] at this
      exact one_ne_zero this
    refine Set.Countable.mono (s₂ := {x0, -x0}) ?_ ((Set.toFinite _).countable)
    rintro y ⟨hy1, hy2⟩
    obtain ⟨c, hc⟩ := fixed_parallel _ (O3.mem_iff M) hdet hMne hx0' (hfix y hy2) hx00
    have hy : y = c • x0 := by
      ext i
      have := congrFun hc i
      simpa using this
    have hnorm : |c| = 1 := by
      have := congrArg (fun z : E => ‖z‖) hy
      simp only [norm_smul, Real.norm_eq_abs, hx0.1, mul_one] at this
      rw [hy1] at this
      exact this.symm
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp hnorm with h | h
    · left; rw [hy, h, one_smul]
    · right; rw [hy, h]; simp

end BT

import Mathlib
import RequestProject.Abstract
import RequestProject.Space
import RequestProject.Free
import RequestProject.Fixed
import RequestProject.Rotate
import RequestProject.Cone

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
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
set_option synthInstance.maxHeartbeats 400000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open Matrix Set Function Metric

namespace BT

/-- The set of *poles*: points of the unit sphere fixed by some nontrivial element of the
free group of rotations. -/
def poles : Set E := {x : E | ‖x‖ = 1 ∧ ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧ Phi w • x = x}

lemma poles_subset : poles ⊆ S2 := fun _ hx => hx.1

/-- No nontrivial word of the free group maps to the identity rotation. -/
lemma Phi_ne_one {w : FreeGroup (Fin 2)} (hw : w ≠ 1) : Phi w ≠ 1 := by
  intro hc
  exact Phi_smul_e2_ne w hw (by rw [hc, one_smul])

/-- There are only countably many poles. -/
lemma poles_countable : poles.Countable := by
  have hsub : poles ⊆ ⋃ w : FreeGroup (Fin 2), {x : E | ‖x‖ = 1 ∧ Phi w • x = x ∧ w ≠ 1} := by
    rintro x ⟨hx1, w, hw, hfix⟩
    exact Set.mem_iUnion.2 ⟨w, hx1, hfix, hw⟩
  refine Set.Countable.mono hsub (Set.countable_iUnion fun w => ?_)
  by_cases hw : w = 1
  · have h : {x : E | ‖x‖ = 1 ∧ Phi w • x = x ∧ w ≠ 1} = ∅ := by
      ext x; simp [hw]
    rw [h]; exact Set.countable_empty
  · refine Set.Countable.mono ?_ (countable_fixed (Phi w) (Phi_det w) (Phi_ne_one hw))
    exact fun x hx => ⟨hx.1, hx.2.1⟩

/-- No pole lies on the `y`-axis: the two points `±e₂` are not fixed by any nontrivial
element of the free group. -/
lemma poles_off_axis : ∀ d ∈ poles, d 0 ≠ 0 ∨ d 2 ≠ 0 := by
  rintro d ⟨hnorm, w, hw, hfix⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨h0, h2⟩ := hcon
  have hsum : d 0 ^ 2 + d 1 ^ 2 + d 2 ^ 2 = 1 := by
    rw [EuclideanSpace.norm_eq] at hnorm
    have h1 : (∑ i, ‖d i‖ ^ 2) = 1 := Real.sqrt_eq_one.mp hnorm
    rw [Fin.sum_univ_three] at h1
    simpa [Real.norm_eq_abs, sq_abs] using h1
  have hd1 : d 1 ^ 2 = 1 := by rw [h0, h2] at hsum; linarith
  set r := d 1 with hr
  have hrne : r ≠ 0 := by intro h; rw [h] at hd1; norm_num at hd1
  have hde : d = r • e2 := by
    ext i
    fin_cases i <;> simp [h0, h2, hr, e2]
  rw [hde, O3.smul_smul_real] at hfix
  exact Phi_smul_e2_ne w hw (smul_right_injective E hrne hfix)

/-- The free group of rotations acts freely on the sphere minus the poles, hence that set is
paradoxical. -/
lemma sphere_sdiff_poles_paradoxical : Paradoxical O3 (S2 \ poles) := by
  refine paradoxical_of_free Phi (S2 \ poles) ?_ ?_
  · rintro w y ⟨x, ⟨hxS, hxp⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · show ‖Phi w • x‖ = 1
      rw [O3.norm_smul]; exact hxS
    · rintro ⟨-, u, hu, hufix⟩
      refine hxp ⟨hxS, w⁻¹ * u * w, ?_, ?_⟩
      · intro hc
        apply hu
        have h : u = w * w⁻¹ := by
          have h2 := congrArg (fun z => w * z * w⁻¹) hc
          simpa [mul_assoc] using h2
        simpa using h
      · rw [map_mul, map_mul, SemigroupAction.mul_smul, SemigroupAction.mul_smul, hufix,
          map_inv, inv_smul_smul]
  · rintro x ⟨hxS, hxp⟩ w hfix
    by_contra hw
    exact hxp ⟨hxS, w, hw, hfix⟩

/-- The countably many poles are absorbed by a suitable rotation about the `y`-axis:
the whole sphere is paradoxical. -/
lemma sphere_paradoxical : Paradoxical O3 S2 := by
  obtain ⟨t, ht⟩ := exists_rotY_disjoint poles poles_countable poles_off_axis
  have hsub : ∀ n : ℕ, ((RY t ^ n) • poles : Set E) ⊆ S2 := by
    rintro n y ⟨x, hx, rfl⟩
    show ‖(RY t ^ n) • x‖ = 1
    rw [O3.norm_smul]; exact hx.1
  obtain ⟨e, hes, het⟩ := exists_equidecomp_sdiff (A := S2) (D := poles) (RY t) hsub ht
  exact Paradoxical.of_equidecomp e.symm het hes sphere_sdiff_poles_paradoxical

/-- Radial extension: the punctured closed unit ball is paradoxical. -/
lemma punctured_ball_paradoxical : Paradoxical O3 (closedBall (0 : E) 1 \ {0}) := by
  rw [← cone_S2]
  exact paradoxical_cone sphere_paradoxical subset_rfl

/-- Finally the centre is absorbed by a screw motion (a rotation about an axis missing the
centre), so the full closed unit ball is paradoxical for the isometry group. -/
lemma ball_paradoxical : Paradoxical Isom (closedBall (0 : E) 1) := by
  have hbase : Paradoxical Isom (closedBall (0 : E) 1 \ {0}) :=
    punctured_ball_paradoxical.map O3.toIsom O3.toIsom_smul
  have hneg : ∀ (N : O3) (y : E), N • (-y) = -(N • y) := by
    intro N y
    have h := O3.smul_smul_real N (-1 : ℝ) y
    simp only [neg_smul, one_smul] at h
    exact h
  set p : E := (1/2 : ℝ) • e2 with hp
  have hnp : ‖p‖ = 1/2 := by
    rw [hp, norm_smul, norm_e2]; norm_num
  set M : O3 := Phi (FreeGroup.of 0) with hM
  set ρ : Isom := (IsometryEquiv.addLeft p) * (O3.toIsom M) * (IsometryEquiv.addLeft (-p)) with hρ
  have hρapp : ∀ x : E, ρ • x = p + M • (x - p) := by
    intro x
    rw [Isom.smul_def, hρ, IsometryEquiv.mul_apply, IsometryEquiv.mul_apply]
    show p + M • (-p + x) = p + M • (x - p)
    rw [neg_add_eq_sub]
  have hpow : ∀ (n : ℕ) (x : E), (ρ ^ n) • x = p + (M ^ n) • (x - p) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ m ih =>
        intro x
        rw [pow_succ', SemigroupAction.mul_smul, ih x, hρapp, pow_succ',
          SemigroupAction.mul_smul]
        simp
  have horb : ∀ n : ℕ, (ρ ^ n) • (0 : E) = p - (M ^ n) • p := by
    intro n
    rw [hpow n 0, zero_sub, hneg]
    abel
  have hball : ∀ n : ℕ, (ρ ^ n) • (0 : E) ∈ closedBall (0 : E) 1 := by
    intro n
    rw [mem_closedBall, dist_zero_right, horb n]
    calc ‖p - (M ^ n) • p‖ ≤ ‖p‖ + ‖(M ^ n) • p‖ := norm_sub_le _ _
      _ = 1 := by rw [O3.norm_smul, hnp]; norm_num
  have hne0 : ∀ n : ℕ, 1 ≤ n → (ρ ^ n) • (0 : E) ≠ 0 := by
    intro n hn hc
    rw [horb n, sub_eq_zero] at hc
    have hword : (FreeGroup.of (0 : Fin 2)) ^ n ≠ 1 := by
      intro h
      have h2 := congrArg
        (FreeGroup.lift (fun i : Fin 2 => if i = 0 then (Multiplicative.ofAdd (1 : ℤ)) else 1)) h
      simp [map_pow] at h2
      omega
    refine Phi_smul_e2_ne _ hword ?_
    rw [map_pow, ← hM]
    have h3 : (M ^ n) • ((1/2 : ℝ) • e2) = (1/2 : ℝ) • ((M ^ n) • e2) :=
      O3.smul_smul_real _ _ _
    rw [hp, h3] at hc
    exact smul_right_injective E (by norm_num : (1/2 : ℝ) ≠ 0) hc.symm
  have hsub : ∀ n : ℕ, (ρ ^ n) • ({0} : Set E) ⊆ closedBall (0 : E) 1 := by
    intro n
    rw [Set.smul_set_singleton]
    simpa using hball n
  have hdisj : ∀ n : ℕ, 1 ≤ n → Disjoint ((ρ ^ n) • ({0} : Set E)) ({0} : Set E) := by
    intro n hn
    rw [Set.smul_set_singleton]
    simpa using hne0 n hn
  obtain ⟨e, hes, het⟩ :=
    exists_equidecomp_sdiff (A := closedBall (0 : E) 1) (D := ({0} : Set E)) ρ hsub hdisj
  exact Paradoxical.of_equidecomp e.symm het hes hbase

end BT

/-- **The Banach–Tarski paradox.** The closed unit ball of `ℝ³` admits a paradoxical
decomposition: it contains two disjoint subsets, each of which can be cut into finitely many
pieces which, after moving each piece by an isometry of `ℝ³`, reassemble to the whole ball.

Here `Equidecomp E Isom` is Mathlib's notion of an equidecomposition for the action of the
isometry group of `E = ℝ³`: a partial bijection of `E` whose source is cut into finitely many
pieces, each of which is moved by a single isometry onto the corresponding piece of the target.
-/
theorem Frontier.Banach_Tarski :
    ∃ f g : Equidecomp BT.E BT.Isom,
      f.source ⊆ Metric.closedBall 0 1 ∧ g.source ⊆ Metric.closedBall 0 1 ∧
        Disjoint f.source g.source ∧
        f.target = Metric.closedBall 0 1 ∧ g.target = Metric.closedBall 0 1 :=
  BT.ball_paradoxical

import RequestProject.Space

/-!
# A free group of rotations of `ℝ³`

The two rotations by `arccos (1/3)` about the `z`-axis and the `x`-axis generate a free group
of rank two. The proof is the classical `3`-adic argument: a nonempty reduced word applied to
the vector `(0, √2, 0)` has the form `(p, q√2, r)/3ᵏ` with `q` not divisible by `3`.
-/

open Matrix Set Function

namespace BT

/-- Rotation by `arccos (1/3)` about the `z`-axis. -/
noncomputable def rA : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1/3, -(2 * Real.sqrt 2/3), 0; 2 * Real.sqrt 2/3, 1/3, 0; 0, 0, 1]

/-- Rotation by `arccos (1/3)` about the `x`-axis. -/
noncomputable def rB : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, 1/3, -(2 * Real.sqrt 2/3); 0, 2 * Real.sqrt 2/3, 1/3]

/-- The two generating rotations. -/
noncomputable def genMat : Fin 2 → Matrix (Fin 3) (Fin 3) ℝ := ![rA, rB]

lemma rA_mem : rA ∈ O3 := by
  rw [Matrix.mem_orthogonalGroup_iff]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rA, Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [h2]

lemma rB_mem : rB ∈ O3 := by
  rw [Matrix.mem_orthogonalGroup_iff]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rB, Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [h2]

lemma det_rA : rA.det = 1 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp [rA, Matrix.det_fin_three]
  nlinarith [h2]

lemma det_rB : rB.det = 1 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp [rB, Matrix.det_fin_three]
  nlinarith [h2]

lemma genMat_mem (i : Fin 2) : genMat i ∈ O3 := by
  fin_cases i
  · exact rA_mem
  · exact rB_mem

lemma det_genMat (i : Fin 2) : (genMat i).det = 1 := by
  fin_cases i
  · exact det_rA
  · exact det_rB

/-- The two generating rotations, as elements of the orthogonal group. -/
noncomputable def gen : Fin 2 → O3 := fun i => ⟨genMat i, genMat_mem i⟩

@[simp] lemma coe_gen (i : Fin 2) : ((gen i : O3) : Matrix (Fin 3) (Fin 3) ℝ) = genMat i := rfl

/-- The homomorphism from the free group of rank two into the rotation group. -/
noncomputable def Phi : FreeGroup (Fin 2) →* O3 := FreeGroup.lift gen

/-! ### The integral `3`-adic invariant -/

/-- The effect of a generator (or its inverse) on the integer coordinates `(p, q, r)`
encoding the vector `(p, q√2, r)/3ᵏ`. -/
def istep (x : Fin 2 × Bool) (v : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  if x.1 = 0 then
    (if x.2 then (v.1 - 4 * v.2.1, 2 * v.1 + v.2.1, 3 * v.2.2)
     else (v.1 + 4 * v.2.1, -2 * v.1 + v.2.1, 3 * v.2.2))
  else
    (if x.2 then (3 * v.1, v.2.1 - 2 * v.2.2, 4 * v.2.1 + v.2.2)
     else (3 * v.1, v.2.1 + 2 * v.2.2, -4 * v.2.1 + v.2.2))

/-- The integer coordinates of the image of `(0, √2, 0)` under a word. -/
def ival : List (Fin 2 × Bool) → ℤ × ℤ × ℤ
  | [] => (0, 1, 0)
  | x :: t => istep x (ival t)

@[simp] lemma ival_nil : ival [] = (0, 1, 0) := rfl

@[simp] lemma ival_cons (x : Fin 2 × Bool) (t : List (Fin 2 × Bool)) :
    ival (x :: t) = istep x (ival t) := rfl

/-- The key `3`-adic invariant: for a nonempty reduced word, the middle coordinate is not
divisible by `3`. -/
theorem ival_mid_not_dvd : ∀ (n : ℕ) (L : List (Fin 2 × Bool)), L.length = n →
    FreeGroup.IsReduced L → L ≠ [] → ¬ ((3 : ℤ) ∣ (ival L).2.1) := by
  intro n
  induction n with
  | zero => intro L hL _ hne; exact absurd (List.length_eq_zero_iff.mp hL) hne
  | succ m ih =>
    intro L hL hred hne
    match L with
    | [x] =>
      rcases x with ⟨i, b⟩
      fin_cases i <;> cases b <;> simp [ival, istep]
    | x :: y :: t =>
      have hIH := ih (y :: t) (by simpa using hL) (FreeGroup.isReduced_cons_cons.mp hred).2
        (by simp)
      have hxy := (FreeGroup.isReduced_cons_cons.mp hred).1
      rcases x with ⟨i, b⟩; rcases y with ⟨j, c⟩
      simp only [ival] at hIH ⊢
      fin_cases i <;> fin_cases j <;> cases b <;> cases c <;>
        simp [istep] at hxy hIH ⊢ <;> omega

/-! ### The real computation -/

/-- The matrix of a letter. -/
noncomputable def matOf (x : Fin 2 × Bool) : Matrix (Fin 3) (Fin 3) ℝ :=
  if x.2 then genMat x.1 else (genMat x.1)ᵀ

/-- The matrix of a word. -/
noncomputable def matWord (L : List (Fin 2 × Bool)) : Matrix (Fin 3) (Fin 3) ℝ :=
  (L.map matOf).prod

@[simp] lemma matWord_nil : matWord [] = 1 := rfl

@[simp] lemma matWord_cons (x : Fin 2 × Bool) (t : List (Fin 2 × Bool)) :
    matWord (x :: t) = matOf x * matWord t := by
  simp [matWord]

lemma matOf_mulVec (x : Fin 2 × Bool) (v : ℤ × ℤ × ℤ) :
    matOf x *ᵥ ![(v.1 : ℝ), (v.2.1 : ℝ) * Real.sqrt 2, (v.2.2 : ℝ)] =
      (3 : ℝ)⁻¹ • ![((istep x v).1 : ℝ), ((istep x v).2.1 : ℝ) * Real.sqrt 2,
        ((istep x v).2.2 : ℝ)] := by
  have h3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  obtain ⟨p, q, r⟩ := v
  rcases x with ⟨i, b⟩
  fin_cases i <;> cases b <;>
    (ext k; fin_cases k <;>
      simp [matOf, genMat, rA, rB, istep, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
      ring_nf; rw [h3]; ring)

/-- The image of `(0, √2, 0)` under the word `L`. -/
theorem matWord_mulVec (L : List (Fin 2 × Bool)) :
    matWord L *ᵥ ![0, Real.sqrt 2, 0] =
      ((3 : ℝ) ^ L.length)⁻¹ •
        ![((ival L).1 : ℝ), ((ival L).2.1 : ℝ) * Real.sqrt 2, ((ival L).2.2 : ℝ)] := by
  induction L with
  | nil =>
      ext k
      fin_cases k <;> simp
  | cons x t ih =>
      rw [matWord_cons, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, matOf_mulVec, smul_smul,
        ival_cons, List.length_cons]
      congr 1
      rw [pow_succ]
      field_simp

lemma star_genMat (i : Fin 2) : star (genMat i) = (genMat i)ᵀ := by
  ext j k
  simp [Matrix.star_apply]

lemma coe_Phi_mk (L : List (Fin 2 × Bool)) :
    ((Phi (FreeGroup.mk L) : O3) : Matrix (Fin 3) (Fin 3) ℝ) = matWord L := by
  induction L with
  | nil =>
      show ((Phi 1 : O3) : Matrix (Fin 3) (Fin 3) ℝ) = matWord []
      rw [map_one, matWord_nil]
      rfl
  | cons x t ih =>
      have hsplit : FreeGroup.mk (x :: t) = FreeGroup.mk [x] * FreeGroup.mk t := by
        rw [FreeGroup.mul_mk]; rfl
      rw [hsplit, map_mul, Submonoid.coe_mul, ih, matWord_cons]
      congr 1
      rcases x with ⟨i, b⟩
      cases b <;> simp [Phi, FreeGroup.lift_mk, gen, matOf, star_genMat]

/-- The second standard basis vector of `ℝ³`. -/
noncomputable def e2 : E := WithLp.toLp 2 ![0, 1, 0]

@[simp] lemma e2_apply (i : Fin 3) : e2 i = ![(0 : ℝ), 1, 0] i := rfl

lemma norm_e2 : ‖e2‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_three]

/-- No nontrivial word of the free group fixes `(0,1,0)`. -/
theorem Phi_smul_e2_ne (w : FreeGroup (Fin 2)) (hw : w ≠ 1) : Phi w • e2 ≠ e2 := by
  intro hcon
  set L := w.toWord with hLdef
  have hL : FreeGroup.mk L = w := FreeGroup.mk_toWord
  have hred : FreeGroup.IsReduced L := FreeGroup.isReduced_toWord
  have hne : L ≠ [] := fun h => hw (FreeGroup.toWord_eq_nil_iff.mp h)
  have hmat : ((Phi w : O3) : Matrix (Fin 3) (Fin 3) ℝ) = matWord L := by
    rw [← hL]; exact coe_Phi_mk L
  -- the matrix fixes `(0,1,0)`
  have hfix : matWord L *ᵥ ![0, 1, 0] = ![0, 1, 0] := by
    funext i
    have := congrFun (congrArg (fun (y : E) (i : Fin 3) => y i) hcon) i
    simpa [O3.smul_apply, hmat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  -- hence it fixes `(0,√2,0)`
  have hscale : ![0, Real.sqrt 2, 0] = Real.sqrt 2 • ![(0 : ℝ), 1, 0] := by
    funext i; fin_cases i <;> simp
  have hfix2 : matWord L *ᵥ ![0, Real.sqrt 2, 0] = ![0, Real.sqrt 2, 0] := by
    rw [hscale, Matrix.mulVec_smul, hfix]
  rw [matWord_mulVec] at hfix2
  have hcoord := congrFun hfix2 1
  simp only [Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul] at hcoord
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  have hq : ((ival L).2.1 : ℝ) = (3 : ℝ) ^ L.length := by
    have h3 : ((3 : ℝ) ^ L.length) ≠ 0 := by positivity
    field_simp at hcoord
    rcases mul_eq_mul_right_iff.mp hcoord with h | h
    · exact h
    · exact absurd h hs2
  have hqz : (ival L).2.1 = 3 ^ L.length := by
    have : ((ival L).2.1 : ℝ) = (((3 ^ L.length : ℤ)) : ℝ) := by push_cast; exact hq
    exact_mod_cast this
  refine ival_mid_not_dvd L.length L rfl hred hne ?_
  rw [hqz]
  exact dvd_pow_self 3 (List.length_eq_zero_iff.not.mpr hne)

/-- All the rotations in the group have determinant one. -/
theorem Phi_det (w : FreeGroup (Fin 2)) :
    ((Phi w : O3) : Matrix (Fin 3) (Fin 3) ℝ).det = 1 := by
  have hmat : ((Phi w : O3) : Matrix (Fin 3) (Fin 3) ℝ) = matWord w.toWord := by
    conv_lhs => rw [← FreeGroup.mk_toWord (x := w)]
    exact coe_Phi_mk _
  rw [hmat]
  induction w.toWord with
  | nil => simp
  | cons x t ih =>
      rw [matWord_cons, Matrix.det_mul, ih, mul_one]
      rcases x with ⟨i, b⟩
      cases b <;> simp [matOf, det_genMat, Matrix.det_transpose]

end BT

import RequestProject.Space

/-!
# Rotations about the `y`-axis, and absorbing a countable set

Given a countable set `D` of points of `ℝ³` none of which lies on the `y`-axis, there is a
rotation `R` about the `y`-axis such that the sets `Rⁿ D` (`n ≥ 1`) are all disjoint from `D`.
-/

open Matrix Set Function Pointwise

namespace BT

/-- Rotation by the angle `t` about the `y`-axis. -/
noncomputable def rotY (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos t, 0, Real.sin t; 0, 1, 0; -Real.sin t, 0, Real.cos t]

lemma rotY_mem (t : ℝ) : rotY t ∈ O3 := by
  rw [Matrix.mem_orthogonalGroup_iff]
  have h := Real.sin_sq_add_cos_sq t
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotY, Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [h]

/-- Rotation about the `y`-axis, as an element of the orthogonal group. -/
noncomputable def RY (t : ℝ) : O3 := ⟨rotY t, rotY_mem t⟩

@[simp] lemma coe_RY (t : ℝ) : ((RY t : O3) : Matrix (Fin 3) (Fin 3) ℝ) = rotY t := rfl

lemma rotY_add (s t : ℝ) : rotY (s + t) = rotY s * rotY t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotY, Matrix.mul_apply, Fin.sum_univ_three, Real.cos_add, Real.sin_add] <;> ring

lemma RY_add (s t : ℝ) : RY (s + t) = RY s * RY t := by
  apply Subtype.ext
  simpa using rotY_add s t

lemma RY_zero : RY 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotY]

lemma RY_pow (t : ℝ) (n : ℕ) : RY t ^ n = RY (n * t) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, RY_zero]
  | succ m ih =>
      rw [pow_succ, ih, ← RY_add]
      congr 1
      push_cast
      ring

lemma RY_smul_apply (t : ℝ) (x : E) :
    ((RY t • x) 0 = Real.cos t * x 0 + Real.sin t * x 2) ∧
    ((RY t • x) 2 = -(Real.sin t) * x 0 + Real.cos t * x 2) := by
  constructor <;>
    simp [O3.smul_apply, rotY, Fin.sum_univ_three]

/-- A rotation about the `y`-axis fixing a point off the `y`-axis is trivial. -/
lemma cos_eq_one_of_fixed {t : ℝ} {y : E} (hy : RY t • y = y) (hax : y 0 ≠ 0 ∨ y 2 ≠ 0) :
    Real.cos t = 1 := by
  obtain ⟨h0, h2⟩ := RY_smul_apply t y
  have e0 : Real.cos t * y 0 + Real.sin t * y 2 = y 0 := by
    rw [← h0, hy]
  have e2 : -(Real.sin t) * y 0 + Real.cos t * y 2 = y 2 := by
    rw [← h2, hy]
  have hpyth := Real.sin_sq_add_cos_sq t
  by_contra hcos
  have hA : (Real.cos t - 1) * y 0 + Real.sin t * y 2 = 0 := by linarith
  have hB : -(Real.sin t) * y 0 + (Real.cos t - 1) * y 2 = 0 := by linarith
  have hne : (2 - 2 * Real.cos t) ≠ 0 := fun hc => hcos (by linarith)
  have h1 : (2 - 2 * Real.cos t) * y 0 = 0 := by
    linear_combination (Real.cos t - 1) * hA - Real.sin t * hB - y 0 * hpyth
  have h2' : (2 - 2 * Real.cos t) * y 2 = 0 := by
    linear_combination Real.sin t * hA + (Real.cos t - 1) * hB - y 2 * hpyth
  rcases hax with h | h
  · exact h ((mul_eq_zero.mp h1).resolve_left hne)
  · exact h ((mul_eq_zero.mp h2').resolve_left hne)

/-- There is a rotation about the `y`-axis moving a given countable set, disjoint from the
`y`-axis, completely off itself, together with all of its positive powers. -/
theorem exists_rotY_disjoint (D : Set E) (hD : D.Countable)
    (hax : ∀ d ∈ D, d 0 ≠ 0 ∨ d 2 ≠ 0) :
    ∃ t : ℝ, ∀ n : ℕ, 1 ≤ n → Disjoint ((RY t ^ n) • D) D := by
  classical
  -- for fixed data, the set of bad angles is countable
  have key : ∀ (m : ℕ) (d d' : E), d ∈ D → d' ∈ D →
      {t : ℝ | (RY t ^ (m + 1)) • d = d'}.Countable := by
    intro m d d' _ hd'
    rcases eq_empty_or_nonempty {t : ℝ | (RY t ^ (m + 1)) • d = d'} with h | ⟨t₀, ht₀⟩
    · rw [h]; exact countable_empty
    · refine Set.Countable.mono (s₂ := range fun k : ℤ => t₀ + k * (2 * Real.pi) / (m + 1)) ?_
        (countable_range _)
      intro t ht
      simp only [mem_setOf_eq] at ht ht₀
      rw [RY_pow] at ht ht₀
      -- `d'` is fixed by the rotation by the difference of the angles
      have hfix : RY ((m + 1 : ℕ) * t - (m + 1 : ℕ) * t₀) • d' = d' := by
        have : RY ((m + 1 : ℕ) * t - (m + 1 : ℕ) * t₀) • (RY ((m + 1 : ℕ) * t₀) • d) =
            RY ((m + 1 : ℕ) * t) • d := by
          rw [← SemigroupAction.mul_smul, ← RY_add]
          congr 2
          ring
        rw [ht₀] at this
        rw [this, ht]
      have hcos := cos_eq_one_of_fixed hfix (hax d' hd')
      obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp hcos
      refine ⟨k, ?_⟩
      have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
      have : ((m : ℝ) + 1) * t - ((m : ℝ) + 1) * t₀ = k * (2 * Real.pi) := by
        push_cast at hk
        linarith [hk]
      field_simp
      linarith [this]
  set B : Set ℝ := ⋃ m : ℕ, ⋃ d ∈ D, ⋃ d' ∈ D, {t : ℝ | (RY t ^ (m + 1)) • d = d'} with hB
  have hBc : B.Countable := by
    refine countable_iUnion fun m => ?_
    refine hD.biUnion fun d hd => ?_
    exact hD.biUnion fun d' hd' => key m d d' hd hd'
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∉ B := by
    by_contra hc
    push_neg at hc
    exact Cardinal.not_countable_real (by rwa [Set.eq_univ_iff_forall.mpr hc] at hBc)
  refine ⟨t, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Set.disjoint_left]
  rintro x ⟨d, hd, rfl⟩ hx'
  exact ht (by
    rw [hB]
    refine mem_iUnion.2 ⟨m, ?_⟩
    refine mem_iUnion₂.2 ⟨d, hd, ?_⟩
    exact mem_iUnion₂.2 ⟨(RY t ^ (m + 1)) • d, hx', rfl⟩)

end BT

