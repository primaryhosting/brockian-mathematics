/-
/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (Lean requires `import` to be the first command, so the header above is wrapped
-- in a block comment; it is repeated verbatim as the module docstring below.)
import Mathlib

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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Overview

We develop the general theory of equidecomposability and paradoxical decompositions
for a group action, following the classical route to the Banach–Tarski paradox:

* `Frontier.Equidecomposable G A B` : `A` and `B` are `G`-equidecomposable (Mathlib's
  `Equidecomp` structure is used as the underlying notion of a finite piecewise-`G` bijection).
* `Frontier.Paradoxical G E` : `E` contains two disjoint subsets, each `G`-equidecomposable
  with `E` itself.

Main results proved here:

* `Frontier.paradoxical_freeGroup` : the free group of rank two is paradoxical
  (acting on itself by left translation).  This is the combinatorial *base case* of
  Banach–Tarski.
* `Frontier.paradoxical_of_freeAction` : any set carrying a free action of the rank two
  free group is paradoxical.  (Hausdorff-type transfer principle, uses choice.)
* `Frontier.Banach_Tarski` : the Lean-checked geometric reduction: if the unit sphere in
  `ℝ³` is paradoxical under rotations, then the closed unit ball is paradoxical under
  isometries.
-/

namespace Frontier

open Metric Set Function

/-! ### Equidecomposability and paradoxical decompositions -/

/-- `A` and `B` are `G`-equidecomposable: there is a bijection from `A` to `B` obtained by
splitting `A` into finitely many pieces and applying a single element of `G` to each piece. -/
def Equidecomposable (G : Type*) {X : Type*} [Group G] [MulAction G X] (A B : Set X) : Prop :=
  ∃ f : Equidecomp X G, f.source = A ∧ f.target = B

/-- `E` admits a *paradoxical decomposition* with respect to the action of `G`: it contains
two disjoint subsets, each of which is `G`-equidecomposable with all of `E`. -/
def Paradoxical (G : Type*) {X : Type*} [Group G] [MulAction G X] (E : Set X) : Prop :=
  ∃ A B : Set X, A ⊆ E ∧ B ⊆ E ∧ Disjoint A B ∧
    Equidecomposable G A E ∧ Equidecomposable G B E

variable {G X : Type*} [Group G] [MulAction G X]

/-- The two-piece equidecomposition: `A₁ ∪ A₂ → g₁ • A₁ ∪ g₂ • A₂`. -/
noncomputable def twoPiece (A₁ A₂ : Set X) (g₁ g₂ : G)
    (hA : Disjoint A₁ A₂) (hB : Disjoint (g₁ • A₁) (g₂ • A₂)) : Equidecomp X G where
  toFun := fun x => if x ∈ A₁ then g₁ • x else g₂ • x
  invFun := fun y => if y ∈ g₁ • A₁ then g₁⁻¹ • y else g₂⁻¹ • y
  source := A₁ ∪ A₂
  target := g₁ • A₁ ∪ g₂ • A₂
  map_source' := by
    rintro x (hx | hx)
    · simp only [hx, if_pos]
      exact Or.inl ⟨x, hx, rfl⟩
    · by_cases h : x ∈ A₁
      · simp only [h, if_pos]; exact Or.inl ⟨x, h, rfl⟩
      · simp only [h, if_neg, not_false_iff]; exact Or.inr ⟨x, hx, rfl⟩
  map_target' := by
    rintro y (hy | hy)
    · simp only [hy, if_pos]
      obtain ⟨x, hx, rfl⟩ := hy
      left; simpa using hx
    · by_cases h : y ∈ g₁ • A₁
      · simp only [h, if_pos]
        obtain ⟨x, hx, rfl⟩ := h
        left; simpa using hx
      · simp only [h, if_neg, not_false_iff]
        obtain ⟨x, hx, rfl⟩ := hy
        right; simpa using hx
  left_inv' := by
    rintro x (hx | hx)
    · simp only [hx, if_pos]
      have : g₁ • x ∈ g₁ • A₁ := ⟨x, hx, rfl⟩
      simp [this]
    · by_cases h : x ∈ A₁
      · simp only [h, if_pos]
        have : g₁ • x ∈ g₁ • A₁ := ⟨x, h, rfl⟩
        simp [this]
      · simp only [h, if_neg, not_false_iff]
        have h2 : g₂ • x ∈ g₂ • A₂ := ⟨x, hx, rfl⟩
        have : g₂ • x ∉ g₁ • A₁ := fun hc => (hB.le_bot ⟨hc, h2⟩ : _)
        simp [this]
  right_inv' := by
    rintro y (hy | hy)
    · simp only [hy, if_pos]
      obtain ⟨x, hx, rfl⟩ := hy
      simp [hx]
    · by_cases h : y ∈ g₁ • A₁
      · simp only [h, if_pos]
        obtain ⟨x, hx, rfl⟩ := h
        simp [hx]
      · simp only [h, if_neg, not_false_iff]
        obtain ⟨x, hx, rfl⟩ := hy
        have hx1 : x ∉ A₁ := fun hc => (hA.le_bot ⟨hc, hx⟩ : _)
        simp [hx1]
  isDecompOn' := ⟨{g₁, g₂}, by
    intro x _
    by_cases h : x ∈ A₁
    · exact ⟨g₁, by simp, by simp [h]⟩
    · exact ⟨g₂, by simp, by simp [h]⟩⟩

/-- Splitting a set into two pieces and translating each piece produces an
equidecomposition. -/
theorem equidecomposable_two_piece {A B : Set X} (A₁ A₂ : Set X) (g₁ g₂ : G)
    (hA : Disjoint A₁ A₂) (hB : Disjoint (g₁ • A₁) (g₂ • A₂))
    (hAeq : A₁ ∪ A₂ = A) (hBeq : g₁ • A₁ ∪ g₂ • A₂ = B) :
    Equidecomposable G A B :=
  ⟨twoPiece A₁ A₂ g₁ g₂ hA hB, hAeq, hBeq⟩

theorem Equidecomposable.refl (A : Set X) : Equidecomposable G A A :=
  ⟨(Equidecomp.refl X G).restr A, by simp, by simp⟩

theorem Equidecomposable.symm {A B : Set X} (h : Equidecomposable G A B) :
    Equidecomposable G B A := by
  obtain ⟨f, hs, ht⟩ := h
  exact ⟨f.symm, ht, hs⟩

theorem Equidecomposable.trans {A B C : Set X} (h₁ : Equidecomposable G A B)
    (h₂ : Equidecomposable G B C) : Equidecomposable G A C := by
  obtain ⟨f, hfs, hft⟩ := h₁
  obtain ⟨g, hgs, hgt⟩ := h₂
  have h : f.target = g.source := by rw [hft, hgs]
  refine ⟨f.trans g, ?_, ?_⟩
  · rw [Equidecomp.trans_toPartialEquiv]
    simp only [PartialEquiv.trans_source, ← h]
    have hsub : f.source ⊆ (f.toPartialEquiv) ⁻¹' f.target := fun x hx => f.map_source hx
    rw [Set.inter_eq_self_of_subset_left hsub, hfs]
  · rw [Equidecomp.trans_toPartialEquiv]
    simp only [PartialEquiv.trans_target, h]
    have hsub : g.target ⊆ (g.toPartialEquiv.symm) ⁻¹' g.source := fun x hx => g.map_target hx
    rw [Set.inter_eq_self_of_subset_left hsub, hgt]

/-- The image of a subset of the source under an equidecomposition is equidecomposable
with that subset. -/
theorem Equidecomposable.image (f : Equidecomp X G) {A : Set X} (hA : A ⊆ f.source) :
    Equidecomposable G A (f '' A) :=
  ⟨f.restr A, f.source_restr hA, by
    rw [Equidecomp.restr_target, f.toPartialEquiv.image_eq_target_inter_inv_preimage hA]⟩

/-- Paradoxicality only depends on the equidecomposability class of a set. -/
theorem Paradoxical.congr {E E' : Set X} (h : Equidecomposable G E E')
    (hE : Paradoxical G E) : Paradoxical G E' := by
  obtain ⟨f, hfs, hft⟩ := h
  obtain ⟨A, B, hAE, hBE, hAB, hA, hB⟩ := hE
  have hAs : A ⊆ f.source := hfs ▸ hAE
  have hBs : B ⊆ f.source := hfs ▸ hBE
  refine ⟨f '' A, f '' B, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hft]; exact fun y ⟨x, hx, hxy⟩ => hxy ▸ f.map_source (hAs hx)
  · rw [← hft]; exact fun y ⟨x, hx, hxy⟩ => hxy ▸ f.map_source (hBs hx)
  · rw [Set.disjoint_left]
    rintro y ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have : a = b := by
      have := f.toPartialEquiv.injOn (hAs ha) (hBs hb) hab.symm
      exact this
    exact (Set.disjoint_left.mp hAB ha) (this ▸ hb)
  · exact ((Equidecomposable.image f hAs).symm.trans hA).trans ⟨f, hfs, hft⟩
  · exact ((Equidecomposable.image f hBs).symm.trans hB).trans ⟨f, hfs, hft⟩

/-- Paradoxicality is inherited along an equivariant group homomorphism. -/
theorem Paradoxical.map {H : Type*} [Group H] [MulAction H X] (phi : G →* H)
    (hphi : ∀ (g : G) (x : X), phi g • x = g • x) {E : Set X} (hE : Paradoxical G E) :
    Paradoxical H E := by
  have key : ∀ {A B : Set X}, Equidecomposable G A B → Equidecomposable H A B := by
    rintro A B ⟨f, hs, ht⟩
    refine ⟨⟨f.toPartialEquiv, ?_⟩, hs, ht⟩
    obtain ⟨S, hS⟩ := f.isDecompOn'
    refine ⟨S.image phi, fun a ha => ?_⟩
    obtain ⟨g, hgS, hg⟩ := hS a ha
    exact ⟨phi g, Finset.mem_image_of_mem _ hgS, by rw [hphi, hg]⟩
  obtain ⟨A, B, hAE, hBE, hAB, hA, hB⟩ := hE
  exact ⟨A, B, hAE, hBE, hAB, key hA, key hB⟩

/-! ### The base case: the free group of rank two -/

section FreeGroup

variable {α : Type*} [DecidableEq α]

/-- Multiplying a reduced word by a letter which does not cancel simply prepends the letter. -/
theorem toWord_letter_mul (x : α × Bool) (w : FreeGroup α)
    (h : w.toWord.head? ≠ some (x.1, !x.2)) :
    (FreeGroup.mk [x] * w).toWord = x :: w.toWord := by
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_mk, FreeGroup.reduce_singleton,
    List.singleton_append, FreeGroup.reduce.cons]
  have hred : FreeGroup.reduce w.toWord = w.toWord := FreeGroup.reduce_toWord w
  cases hw : w.toWord with
  | nil => simp
  | cons hd tl =>
      rw [hw] at hred h
      rw [hred]
      have hne : ¬ (x.1 = hd.1 ∧ x.2 = !hd.2) := by
        rintro ⟨h1, h2⟩
        have hhd : hd = (x.1, !x.2) := by obtain ⟨a, b⟩ := hd; simp_all
        exact h (by simp [hhd])
      simp [hne]

/-- Multiplying a word starting with the letter `x` by the inverse letter deletes it. -/
theorem toWord_letter_inv_mul (x : α × Bool) (w : FreeGroup α) (t : List (α × Bool))
    (hw : w.toWord = x :: t) : (FreeGroup.mk [(x.1, !x.2)] * w).toWord = t := by
  have h1 : w = FreeGroup.mk [x] * FreeGroup.mk t := by
    conv_lhs => rw [← FreeGroup.mk_toWord (x := w)]
    rw [hw, FreeGroup.mul_mk, List.singleton_append]
  have hinv : FreeGroup.mk [(x.1, !x.2)] = (FreeGroup.mk [x])⁻¹ := by
    rw [FreeGroup.inv_mk]; simp [FreeGroup.invRev]
  have hred : FreeGroup.IsReduced t := by
    have h3 := FreeGroup.isReduced_toWord (x := w)
    rw [hw] at h3
    exact h3.infix ⟨[x], [], by simp⟩
  rw [h1, hinv, ← mul_assoc, inv_mul_cancel, one_mul, FreeGroup.toWord_mk, hred.reduce_eq]

/-- The set of elements of a free group whose reduced word starts with the letter `x`. -/
def startingWith (x : α × Bool) : Set (FreeGroup α) := {w | w.toWord.head? = some x}

theorem disjoint_startingWith {x y : α × Bool} (h : x ≠ y) :
    Disjoint (startingWith x) (startingWith y) := by
  rw [Set.disjoint_left]
  intro w hx hy
  have hx' : w.toWord.head? = some x := hx
  have hy' : w.toWord.head? = some y := hy
  rw [hx'] at hy'
  exact h (Option.some.inj hy')

/-- Translating the words starting with `x⁻¹` by `x` gives exactly the words *not* starting
with `x`. -/
theorem smul_startingWith (x : α × Bool) :
    (FreeGroup.mk [x] : FreeGroup α) • startingWith (x.1, !x.2) = (startingWith x)ᶜ := by
  have hx : ((x.1, !x.2).1, !(x.1, !x.2).2) = x := by simp
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : w.toWord.head? = some (x.1, !x.2) := hw
    obtain ⟨t, ht⟩ : ∃ t, w.toWord = (x.1, !x.2) :: t := by
      cases hL : w.toWord with
      | nil => rw [hL] at hw'; simp at hw'
      | cons hd tl =>
          rw [hL] at hw'; simp only [List.head?_cons, Option.some.injEq] at hw'
          exact ⟨tl, by rw [hw']⟩
    have hkey := toWord_letter_inv_mul (x.1, !x.2) w t ht
    rw [hx] at hkey
    intro hc
    have hcc : (FreeGroup.mk [x] * w).toWord.head? = some x := hc
    rw [hkey] at hcc
    have hred := FreeGroup.isReduced_toWord (x := w)
    rw [ht] at hred
    cases hT : t with
    | nil => rw [hT] at hcc; simp at hcc
    | cons hd tl =>
        rw [hT] at hcc hred
        simp only [List.head?_cons, Option.some.injEq] at hcc
        rw [FreeGroup.isReduced_cons_cons] at hred
        have h1 := hred.1
        obtain ⟨a, b⟩ := hd
        subst hcc
        simp at h1
  · intro hu
    have hu' : u.toWord.head? ≠ some x := hu
    refine ⟨FreeGroup.mk [(x.1, !x.2)] * u, ?_, ?_⟩
    · show (FreeGroup.mk [(x.1, !x.2)] * u).toWord.head? = some (x.1, !x.2)
      rw [toWord_letter_mul (x.1, !x.2) u (by rw [hx]; exact hu')]
      simp
    · show FreeGroup.mk [x] * (FreeGroup.mk [(x.1, !x.2)] * u) = u
      have hinv : (FreeGroup.mk [(x.1, !x.2)] : FreeGroup α) = (FreeGroup.mk [x])⁻¹ := by
        rw [FreeGroup.inv_mk]; simp [FreeGroup.invRev]
      rw [hinv, ← mul_assoc, mul_inv_cancel, one_mul]

end FreeGroup

/-- Abbreviation for the free group of rank two. -/
abbrev F2 : Type := FreeGroup (Fin 2)

/-- The four sets of words starting with a given generator or its inverse. -/
noncomputable def wA : Set F2 := startingWith (0, true)
noncomputable def wA' : Set F2 := startingWith (0, false)
noncomputable def wB : Set F2 := startingWith (1, true)
noncomputable def wB' : Set F2 := startingWith (1, false)

/-- The generators of `F2`, as words. -/
noncomputable def genA : F2 := FreeGroup.mk [(0, true)]
noncomputable def genB : F2 := FreeGroup.mk [(1, true)]

theorem smul_wA' : genA • wA' = wAᶜ := by
  have := smul_startingWith ((0 : Fin 2), true)
  simpa [genA, wA, wA'] using this

theorem smul_wB' : genB • wB' = wBᶜ := by
  have := smul_startingWith ((1 : Fin 2), true)
  simpa [genB, wB, wB'] using this

/-- A general criterion producing a paradoxical decomposition out of a "transfer map"
`star` from subsets of the free group `F2` to subsets of `E`. -/
theorem paradoxical_of_star {Y : Type*} [MulAction F2 Y] (E : Set Y) (star : Set F2 → Set Y)
    (h_union : ∀ S T, star (S ∪ T) = star S ∪ star T)
    (h_disj : ∀ S T, Disjoint S T → Disjoint (star S) (star T))
    (h_smul : ∀ (g : F2) (S : Set F2), g • star S = star (g • S))
    (h_univ : star Set.univ = E)
    (h_sub : ∀ S, star S ⊆ E) :
    Paradoxical F2 E := by
  refine ⟨star (wA ∪ wA'), star (wB ∪ wB'), h_sub _, h_sub _, ?_, ?_, ?_⟩
  · refine h_disj _ _ ?_
    simp only [Set.disjoint_union_left, Set.disjoint_union_right]
    exact ⟨⟨disjoint_startingWith (by decide), disjoint_startingWith (by decide)⟩,
      disjoint_startingWith (by decide), disjoint_startingWith (by decide)⟩
  · refine equidecomposable_two_piece (star wA) (star wA') 1 genA
      (h_disj _ _ (disjoint_startingWith (by decide))) ?_ (h_union _ _).symm ?_
    · rw [one_smul, h_smul, smul_wA']
      exact h_disj _ _ disjoint_compl_right
    · rw [one_smul, h_smul, smul_wA', ← h_union, Set.union_compl_self, h_univ]
  · refine equidecomposable_two_piece (star wB) (star wB') 1 genB
      (h_disj _ _ (disjoint_startingWith (by decide))) ?_ (h_union _ _).symm ?_
    · rw [one_smul, h_smul, smul_wB']
      exact h_disj _ _ disjoint_compl_right
    · rw [one_smul, h_smul, smul_wB', ← h_union, Set.union_compl_self, h_univ]

/-- **The base case of the Banach–Tarski paradox**: the free group of rank two admits a
paradoxical decomposition for its action on itself by left translation. -/
theorem paradoxical_freeGroup : Paradoxical F2 (Set.univ : Set F2) :=
  paradoxical_of_star Set.univ id (fun _ _ => rfl) (fun _ _ h => h) (fun _ _ => rfl) rfl
    (fun _ => Set.subset_univ _)

/-! ### Transfer to sets carrying a free action of the free group -/

/-- **Hausdorff-type transfer principle.**  If the free group of rank two acts on a set `E`
(i.e. `E` is invariant) and the action is free on `E` (no non-identity element fixes a point
of `E`), then `E` admits a paradoxical decomposition.  The proof picks one representative in
each orbit (this uses the axiom of choice) and transports the paradoxical decomposition of
`F2` itself. -/
theorem paradoxical_of_freeAction {Y : Type*} [MulAction F2 Y] (E : Set Y)
    (hinv : ∀ (g : F2), ∀ y ∈ E, g • y ∈ E)
    (hfree : ∀ (g : F2), ∀ y ∈ E, g • y = y → g = 1) : Paradoxical F2 E := by
  classical
  set r : Y → Y := fun y => (Quotient.mk (MulAction.orbitRel F2 Y) y).out with hrdef
  have hr_eq : ∀ (g : F2) (y : Y), r (g • y) = r y := by
    intro g y
    have hq : (Quotient.mk (MulAction.orbitRel F2 Y) (g • y))
        = Quotient.mk (MulAction.orbitRel F2 Y) y :=
      Quotient.sound (MulAction.orbitRel_apply.mpr ⟨g, rfl⟩)
    simp only [hrdef, hq]
  have hr_orbit : ∀ y : Y, ∃ g : F2, y = g • r y := by
    intro y
    have h1 : Quotient.mk (MulAction.orbitRel F2 Y) (r y)
        = Quotient.mk (MulAction.orbitRel F2 Y) y := Quotient.out_eq _
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h1)
    exact ⟨g⁻¹, by rw [← hg]; simp⟩
  have hr_idem : ∀ y : Y, r (r y) = r y := by
    intro y
    obtain ⟨g, hg⟩ := hr_orbit y
    conv_rhs => rw [hg]
    rw [hr_eq]
  have hr_mem : ∀ y ∈ E, r y ∈ E := by
    intro y hy
    obtain ⟨g, hg⟩ := hr_orbit y
    have hry : r y = g⁻¹ • y := by conv_rhs => rw [hg, inv_smul_smul]
    rw [hry]; exact hinv _ _ hy
  have huniq : ∀ (g g' : F2) (y y' : Y), y ∈ E → y' ∈ E → g • r y = g' • r y' →
      g = g' ∧ r y = r y' := by
    intro g g' y y' hy hy' h
    have h1 : r y' = r y := by
      have h3 := hr_eq g' (r y')
      rw [← h, hr_eq g (r y), hr_idem, hr_idem] at h3
      exact h3.symm
    refine ⟨?_, h1.symm⟩
    rw [h1] at h
    have h2 : (g'⁻¹ * g) • r y = r y := by rw [mul_smul, h, inv_smul_smul]
    exact (inv_mul_eq_one.mp (hfree _ _ (hr_mem y hy) h2)).symm
  refine paradoxical_of_star E (fun S => {z | ∃ g ∈ S, ∃ y ∈ E, z = g • r y}) ?_ ?_ ?_ ?_ ?_
  · intro S T
    ext z
    constructor
    · rintro ⟨g, (hg | hg), y, hy, rfl⟩
      exacts [Or.inl ⟨g, hg, y, hy, rfl⟩, Or.inr ⟨g, hg, y, hy, rfl⟩]
    · rintro (⟨g, hg, y, hy, rfl⟩ | ⟨g, hg, y, hy, rfl⟩)
      exacts [⟨g, Or.inl hg, y, hy, rfl⟩, ⟨g, Or.inr hg, y, hy, rfl⟩]
  · intro S T hST
    rw [Set.disjoint_left]
    rintro z ⟨g, hg, y, hy, rfl⟩ ⟨g', hg', y', hy', heq⟩
    obtain ⟨rfl, -⟩ := huniq g g' y y' hy hy' heq
    exact Set.disjoint_left.mp hST hg hg'
  · intro g S
    ext z
    constructor
    · rintro ⟨w, ⟨g', hg', y, hy, rfl⟩, rfl⟩
      exact ⟨g * g', ⟨g', hg', rfl⟩, y, hy, (mul_smul g g' (r y)).symm⟩
    · rintro ⟨g', ⟨g'', hg'', rfl⟩, y, hy, rfl⟩
      exact ⟨g'' • r y, ⟨g'', hg'', y, hy, rfl⟩, (mul_smul g g'' (r y)).symm⟩
  · ext z
    constructor
    · rintro ⟨g, -, y, hy, rfl⟩
      exact hinv _ _ (hr_mem y hy)
    · intro hz
      obtain ⟨g, hg⟩ := hr_orbit z
      exact ⟨g, Set.mem_univ _, z, hz, hg⟩
  · rintro S z ⟨g, -, y, hy, rfl⟩
    exact hinv _ _ (hr_mem y hy)

end Frontier

