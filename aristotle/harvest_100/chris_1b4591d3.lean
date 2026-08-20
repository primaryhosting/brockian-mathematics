/-
# The infinite Ramsey theorem

Mathlib (as of this project's pinned version) contains no form of Ramsey's theorem, so we develop
the infinite version here, for colourings of `n`-element subsets of `ℕ` with `k` colours.

An infinite homogeneous set is presented as the range of a strictly monotone function `f : ℕ → ℕ`.
-/
import Mathlib

set_option autoImplicit false

namespace Frontier

open Finset

/-- `Homogeneous n c f a` says that every `n`-element subset of the range of `f` has colour `a`. -/
def Homogeneous {k : ℕ} (n : ℕ) (c : Finset ℕ → Fin k) (f : ℕ → ℕ) (a : Fin k) : Prop :=
  ∀ s : Finset ℕ, s.card = n → c (s.image f) = a

/-- A finite subset of the range of a map is the image of a finite set of the same
cardinality. -/
lemma exists_preimage_finset {g : ℕ → ℕ} (t : Finset ℕ)
    (ht : ∀ x ∈ t, x ∈ Set.range g) : ∃ s : Finset ℕ, s.card = t.card ∧ s.image g = t := by
  classical
  refine ⟨t.image (Function.invFun g), ?_, ?_⟩
  · apply Finset.card_image_of_injOn
    intro x hx z hz hxz
    have hx' := Function.invFun_eq (ht x hx)
    have hz' := Function.invFun_eq (ht z hz)
    rw [← hx', ← hz', hxz]
  · rw [Finset.image_image]
    refine (Finset.image_congr ?_).trans Finset.image_id
    intro x hx
    exact Function.invFun_eq (ht x hx)

/-- One step of the standard construction: given the Ramsey property in dimension `n`, and a
strictly monotone `g`, we can thin out the range of `g` past its first element `g 0` so that the
colour of `{g 0} ∪ t` is constant for `n`-element subsets `t` of the thinned range. -/
lemma ramsey_step {k n : ℕ}
    (IH : ∀ d : Finset ℕ → Fin k, ∃ f : ℕ → ℕ, StrictMono f ∧ ∃ a : Fin k, Homogeneous n d f a)
    (c : Finset ℕ → Fin k) (g : ℕ → ℕ) (hg : StrictMono g) :
    ∃ (g' : ℕ → ℕ) (a : Fin k), StrictMono g' ∧ (∀ i, g 0 < g' i) ∧
      (∀ i, ∃ j, g' i = g j) ∧
      ∀ s : Finset ℕ, s.card = n → c (insert (g 0) (s.image g')) = a := by
  classical
  obtain ⟨h, hh, α, hom⟩ := IH fun t => c (insert (g 0) (t.image fun i => g (i + 1)))
  refine ⟨fun i => g (h i + 1), α, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact hg (by have := hh hij; omega)
  · intro i
    exact hg (by omega)
  · intro i
    exact ⟨h i + 1, rfl⟩
  · intro s hs
    have h2 := hom s hs
    simp only [Finset.image_image] at h2
    exact h2

/-- **Infinite Ramsey theorem.** For every colouring of the finite subsets of `ℕ` with `k` colours
there is an infinite set (the range of a strictly monotone `f`) all of whose `n`-element subsets
receive the same colour. -/
theorem infinite_ramsey (n k : ℕ) (c : Finset ℕ → Fin k) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∃ a : Fin k, Homogeneous n c f a := by
  classical
  induction n generalizing c with
  | zero =>
      refine ⟨id, strictMono_id, c ∅, ?_⟩
      intro s hs
      rw [Finset.card_eq_zero] at hs
      subst hs
      simp
  | succ n IH =>
      rcases isEmpty_or_nonempty (Fin k) with hk | hk
      · exact (hk.false (c ∅)).elim
      -- one step of thinning, packaged for the recursion
      have key : ∀ g : {g : ℕ → ℕ // StrictMono g},
          ∃ p : {g : ℕ → ℕ // StrictMono g} × Fin k,
            (∀ i, g.1 0 < p.1.1 i) ∧ (∀ i, ∃ j, p.1.1 i = g.1 j) ∧
            ∀ s : Finset ℕ, s.card = n → c (insert (g.1 0) (s.image p.1.1)) = p.2 := by
        intro g
        obtain ⟨g', b, hg'mono, h1, h2, h3⟩ := ramsey_step IH c g.1 g.2
        exact ⟨(⟨g', hg'mono⟩, b), h1, h2, h3⟩
      choose F hF1 hF2 hF3 using key
      -- the nested sequence of reservoirs
      set G : ℕ → {g : ℕ → ℕ // StrictMono g} :=
        fun i => Nat.rec ⟨id, strictMono_id⟩ (fun _ g => (F g).1) i with hGdef
      set a : ℕ → ℕ := fun i => (G i).1 0 with hadef
      set α : ℕ → Fin k := fun i => (F (G i)).2 with hαdef
      have hrange : ∀ j i, i ≤ j → ∀ x, ∃ y, (G j).1 x = (G i).1 y := by
        intro j
        induction j with
        | zero =>
            intro i hi x
            obtain rfl : i = 0 := Nat.le_zero.mp hi
            exact ⟨x, rfl⟩
        | succ j ihj =>
            intro i hi x
            rcases eq_or_lt_of_le hi with rfl | h
            · exact ⟨x, rfl⟩
            · have hij : i ≤ j := Nat.lt_succ_iff.mp h
              obtain ⟨y, hy⟩ := hF2 (G j) x
              obtain ⟨z, hz⟩ := ihj i hij y
              exact ⟨z, by rw [show (G (j + 1)).1 x = (F (G j)).1.1 x from rfl, hy, hz]⟩
      have hamono : StrictMono a := strictMono_nat_of_lt_succ fun i => hF1 (G i) 0
      have hkey : ∀ i (t : Finset ℕ), t.card = n → (∀ x ∈ t, x ∈ Set.range (G (i + 1)).1) →
          c (insert (a i) t) = α i := by
        intro i t htc hmem
        obtain ⟨s, hs, hst⟩ := exists_preimage_finset t hmem
        rw [← hst]
        exact hF3 (G i) s (by rw [hs, htc])
      -- pigeonhole on the colours attached to the successive first elements
      obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber α
      have hinf : {i | α i = y}.Infinite := Set.infinite_coe_iff.mp hy
      set φ := Nat.nth (fun i => α i = y) with hφdef
      have hφ : StrictMono φ := Nat.nth_strictMono hinf
      have hφmem : ∀ i, α (φ i) = y := Nat.nth_mem_of_infinite hinf
      have hinj : Function.Injective fun i => a (φ i) := fun x z h => (hamono.comp hφ).injective h
      refine ⟨fun i => a (φ i), hamono.comp hφ, y, ?_⟩
      intro s hs
      have hne : s.Nonempty := Finset.card_pos.mp (by omega)
      have hi0 : s.min' hne ∈ s := s.min'_mem hne
      have himg : s.image (fun i => a (φ i))
          = insert (a (φ (s.min' hne))) ((s.erase (s.min' hne)).image fun i => a (φ i)) := by
        conv_lhs => rw [← Finset.insert_erase hi0]
        rw [Finset.image_insert]
      rw [himg, hkey (φ (s.min' hne))]
      · exact hφmem _
      · rw [Finset.card_image_of_injective _ hinj, Finset.card_erase_of_mem hi0, hs]
        omega
      · intro x hx
        simp only [Finset.mem_image, Finset.mem_erase] at hx
        obtain ⟨z, ⟨hzne, hzs⟩, rfl⟩ := hx
        have hlt : s.min' hne < z := lt_of_le_of_ne (s.min'_le z hzs) (Ne.symm hzne)
        have hle : φ (s.min' hne) + 1 ≤ φ z := hφ hlt
        obtain ⟨w, hw⟩ := hrange (φ z) (φ (s.min' hne) + 1) hle 0
        exact ⟨w, hw.symm⟩

end Frontier

/-
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is the requested header comment; Lean 4 does not allow a module docstring
`/-! ... -/` to precede `import`, so it is written as an ordinary block comment.)

The Paris–Harrington theorem consists of two halves:

* the *strengthened finite Ramsey theorem* is **true**;
* it is **not provable in Peano arithmetic**.

The second half is a metamathematical statement about the theory `PA`; formalising it would require
a full development of first-order arithmetic together with the Paris–Harrington indicator argument,
and it is not attempted here.  What is formalised and proved here is the mathematical content: the
strengthened finite Ramsey theorem itself, `Frontier.Paris_Harrington`, proved (as in the original
argument) from the infinite Ramsey theorem by a compactness argument.  Mathlib contains no Ramsey
theorem, so the infinite Ramsey theorem is developed from scratch in
`RequestProject.InfiniteRamsey`; the compactness step is carried out with a non-principal
ultrafilter (`Filter.hyperfilter ℕ`) instead of König's lemma.
-/
import RequestProject.InfiniteRamsey

set_option autoImplicit false

namespace Frontier

open Finset Filter

/-- A finite set of natural numbers is *relatively large* if it is nonempty and has at least as
many elements as its least element. -/
def RelativelyLarge (Y : Finset ℕ) : Prop := ∃ h : Y.Nonempty, Y.min' h ≤ Y.card

/-- `Y` witnesses the strengthened finite Ramsey property for the colouring `c` of `n`-element
sets inside `{1, …, N}`, with size demand `m`: it is a relatively large homogeneous subset of
`{1, …, N}` with at least `m` elements. -/
def IsPHWitness {k : ℕ} (n m N : ℕ) (c : Finset ℕ → Fin k) (Y : Finset ℕ) : Prop :=
  Y ⊆ Finset.Icc 1 N ∧ m ≤ Y.card ∧ RelativelyLarge Y ∧
    ∃ a : Fin k, ∀ t ⊆ Y, t.card = n → c t = a

/-- The **strengthened finite Ramsey theorem** (the Paris–Harrington statement): for all `n, k, m`
there is `N` such that every `k`-colouring of the `n`-element subsets of `{1, …, N}` admits a
relatively large homogeneous subset of `{1, …, N}` with at least `m` elements. -/
def StrengthenedFiniteRamsey : Prop :=
  ∀ n k m : ℕ, ∃ N : ℕ, ∀ c : Finset ℕ → Fin k, ∃ Y : Finset ℕ, IsPHWitness n m N c Y

/-- Along an ultrafilter, a family of colourings has a limit colouring. -/
lemma exists_limit_coloring {k : ℕ} (U : Ultrafilter ℕ) (F : ℕ → Finset ℕ → Fin k) :
    ∃ c : Finset ℕ → Fin k, ∀ s : Finset ℕ, {N | F N s = c s} ∈ U := by
  have key : ∀ s : Finset ℕ, ∃ b : Fin k, ∀ᶠ N in (U : Filter ℕ), F N s = b := fun s =>
    Ultrafilter.eventually_exists_iff.mp (Filter.Eventually.of_forall fun N => ⟨F N s, rfl⟩)
  choose c hc using key
  exact ⟨c, hc⟩

/-- Finitely many of the ultrafilter conditions can be met simultaneously. -/
lemma limit_coloring_finite_agreement {k : ℕ} (U : Ultrafilter ℕ) (F : ℕ → Finset ℕ → Fin k)
    (c : Finset ℕ → Fin k) (hc : ∀ s : Finset ℕ, {N | F N s = c s} ∈ U)
    (T : Finset (Finset ℕ)) : {N | ∀ s ∈ T, F N s = c s} ∈ U :=
  (Filter.eventually_all_finset T).mpr fun s _ => hc s

/-- From an infinite homogeneous set one extracts a relatively large finite homogeneous set of any
prescribed size, consisting of positive numbers. -/
lemma exists_relatively_large_of_homogeneous {k n m : ℕ} (c : Finset ℕ → Fin k) (f : ℕ → ℕ)
    (hf : StrictMono f) (a : Fin k) (hom : Homogeneous n c f a) :
    ∃ Y : Finset ℕ, m ≤ Y.card ∧ RelativelyLarge Y ∧ (∀ y ∈ Y, 1 ≤ y) ∧
      ∀ t ⊆ Y, t.card = n → c t = a := by
  classical
  have hsucc : Function.Injective fun i : ℕ => i + 1 := fun x y h => by simpa using h
  set f' : ℕ → ℕ := fun i => f (i + 1) with hf'def
  have hf' : StrictMono f' := fun i j hij => hf (by omega)
  have hpos : ∀ i, 1 ≤ f' i := by
    intro i
    have he : f' i = f (i + 1) := rfl
    have h1 : f 0 < f 1 := hf (by omega)
    have h2 : f 1 ≤ f (i + 1) := hf.monotone (by omega)
    omega
  set M : ℕ := max m (f' 0) with hM
  refine ⟨(Finset.range M).image f', ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hf'.injective, Finset.card_range]
    exact le_max_left _ _
  · have hMpos : 0 < M := lt_of_lt_of_le (hpos 0) (le_max_right _ _)
    have hmem : f' 0 ∈ (Finset.range M).image f' :=
      Finset.mem_image_of_mem _ (Finset.mem_range.mpr hMpos)
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [Finset.card_image_of_injective _ hf'.injective, Finset.card_range]
    exact le_trans (Finset.min'_le _ _ hmem) (le_max_right _ _)
  · intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact hpos i
  · intro t ht htc
    have hrange : ∀ x ∈ t, x ∈ Set.range f' := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (ht hx)
      exact ⟨i, rfl⟩
    obtain ⟨s, hs, rfl⟩ := exists_preimage_finset t hrange
    have h2 := hom (s.image fun i => i + 1) (by
      rw [Finset.card_image_of_injective _ hsucc]; omega)
    rw [Finset.image_image] at h2
    exact h2

/-- **Paris–Harrington: the strengthened finite Ramsey theorem is true.**

For all `n, k, m` there is an `N` such that every colouring of the `n`-element subsets of
`{1, …, N}` with `k` colours has a homogeneous set `Y ⊆ {1, …, N}` with at least `m` elements
which is relatively large, i.e. `min Y ≤ |Y|`. -/
theorem Paris_Harrington : StrengthenedFiniteRamsey := by
  classical
  intro n k m
  by_contra hcon
  push_neg at hcon
  choose F hF using hcon
  obtain ⟨c, hc⟩ := exists_limit_coloring (Filter.hyperfilter ℕ) F
  obtain ⟨f, hf, a, hom⟩ := infinite_ramsey n k c
  obtain ⟨Y, hYm, hYlarge, hYpos, hYhom⟩ :=
    exists_relatively_large_of_homogeneous (m := m) c f hf a hom
  have h1 : {N | ∀ s ∈ Y.powersetCard n, F N s = c s} ∈ (Filter.hyperfilter ℕ : Filter ℕ) :=
    limit_coloring_finite_agreement _ F c hc _
  have h2 : {N | ∀ y ∈ Y, y ≤ N} ∈ (Filter.hyperfilter ℕ : Filter ℕ) := by
    refine Nat.hyperfilter_le_atTop ?_
    filter_upwards [Filter.eventually_ge_atTop (Y.sup id)] with N hN y hy
    exact le_trans (Finset.le_sup (f := id) hy) hN
  obtain ⟨N, hN1, hN2⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 h2)
  refine hF N Y ⟨?_, hYm, hYlarge, a, ?_⟩
  · intro y hy
    exact Finset.mem_Icc.mpr ⟨hYpos y hy, hN2 y hy⟩
  · intro t ht htc
    rw [hN1 t (Finset.mem_powersetCard.mpr ⟨ht, htc⟩)]
    exact hYhom t ht htc

/-- The ordinary finite Ramsey theorem is a consequence: for all `n, k, m` there is `N` such that
every `k`-colouring of the `n`-element subsets of `{1, …, N}` has a homogeneous subset of
`{1, …, N}` with at least `m` elements. -/
theorem finite_ramsey (n k m : ℕ) :
    ∃ N : ℕ, ∀ c : Finset ℕ → Fin k, ∃ Y ⊆ Finset.Icc 1 N,
      m ≤ Y.card ∧ ∃ a : Fin k, ∀ t ⊆ Y, t.card = n → c t = a := by
  obtain ⟨N, hN⟩ := Paris_Harrington n k m
  refine ⟨N, fun c => ?_⟩
  obtain ⟨Y, hsub, hcard, -, hhom⟩ := hN c
  exact ⟨Y, hsub, hcard, hhom⟩

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

