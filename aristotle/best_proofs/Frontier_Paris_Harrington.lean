import Mathlib
/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The strengthened finite Ramsey theorem (Paris–Harrington)

A finite set `Y ⊆ ℕ` of positive integers is *relatively large* if its number of
elements is at least its least element.  The Paris–Harrington statement says:

> for all `n, k, m` there is `N` such that for every colouring `c` of the
> `n`-element subsets of `{1, …, N}` with `k` colours there is a relatively large
> `Y ⊆ {1, …, N}` with `m ≤ |Y|` all of whose `n`-element subsets have the same
> colour.

This is `Frontier.Paris_Harrington` below, and it is proved here in full (via the
infinite Ramsey theorem proved in Part 1 below together with an
ultrafilter compactness argument).

The second half of the Paris–Harrington theorem — that this statement is *not*
provable in first-order Peano arithmetic — is a metamathematical statement about
a formal proof system, not a statement of ordinary mathematics; it is not
formalized here.  What is formalized and proved here is the truth of the
strengthened finite Ramsey theorem.
-/

namespace Frontier

open Finset Filter

/-! ## Part 1: the infinite Ramsey theorem for hypergraphs -/

/-- `H` is homogeneous for the colouring `c` in dimension `n`: all `n`-element
subsets of `H` receive the same colour. -/
def SetHomog (n : ℕ) {k : ℕ} (c : Finset ℕ → Fin k) (H : Set ℕ) : Prop :=
  ∀ A B : Finset ℕ, ↑A ⊆ H → A.card = n → ↑B ⊆ H → B.card = n → c A = c B

private lemma ramsey_step {k n : ℕ} (c : Finset ℕ → Fin k)
    (F : ∀ T : Set ℕ, T.Infinite → Set ℕ)
    (hFsub : ∀ T h, F T h ⊆ T) (hFinf : ∀ T h, (F T h).Infinite)
    (hFgt : ∀ T h, ∀ x ∈ F T h, sInf T < x)
    (hFhom : ∀ T h, SetHomog n (fun A => c (insert (sInf T) A)) (F T h))
    (S : Set ℕ) (hS : S.Infinite) :
    ∃ H ⊆ S, H.Infinite ∧ SetHomog (n + 1) c H := by
  classical
  let g : {T : Set ℕ // T.Infinite} → {T : Set ℕ // T.Infinite} :=
    fun T => ⟨F T.1 T.2, hFinf T.1 T.2⟩
  let Ss : ℕ → {T : Set ℕ // T.Infinite} := fun i => g^[i] ⟨S, hS⟩
  have hSs0 : (Ss 0).1 = S := rfl
  have hstep : ∀ i, (Ss (i + 1)).1 = F (Ss i).1 (Ss i).2 := by
    intro i
    show (g^[i + 1] ⟨S, hS⟩).1 = _
    rw [Function.iterate_succ_apply']
  set a : ℕ → ℕ := fun i => sInf (Ss i).1 with ha
  have hamem : ∀ i, a i ∈ (Ss i).1 := by
    intro i
    exact Nat.sInf_mem ((Ss i).2.nonempty)
  have hsub : ∀ i, (Ss (i + 1)).1 ⊆ (Ss i).1 := by
    intro i
    rw [hstep i]
    exact hFsub _ _
  have hmono : ∀ i j, i ≤ j → (Ss j).1 ⊆ (Ss i).1 := by
    intro i j hij
    induction j with
    | zero => simpa using (Nat.le_zero.mp hij) ▸ subset_rfl
    | succ j ih =>
        rcases Nat.lt_or_ge i (j + 1) with h | h
        · exact (hsub j).trans (ih (Nat.lt_succ_iff.mp h))
        · have : i = j + 1 := le_antisymm hij h
          subst this; exact subset_rfl
  have hgt : ∀ i, ∀ x ∈ (Ss (i + 1)).1, a i < x := by
    intro i x hx
    rw [hstep i] at hx
    exact hFgt _ _ x hx
  have hstrict : StrictMono a := by
    apply strictMono_nat_of_lt_succ
    intro i
    exact hgt i (a (i + 1)) (hamem (i + 1))
  have hainj : Function.Injective a := hstrict.injective
  have hain : ∀ i j, i + 1 ≤ j → a j ∈ (Ss (i + 1)).1 := by
    intro i j hij
    exact hmono _ _ hij (hamem j)
  -- the canonical `n`-element set of later points
  set B0 : ℕ → Finset ℕ := fun i => (Finset.Icc (i + 1) (i + n)).image a with hB0
  have hB0card : ∀ i, (B0 i).card = n := by
    intro i
    rw [hB0]
    rw [Finset.card_image_of_injective _ hainj, Nat.card_Icc]
    omega
  have hB0sub : ∀ i, ↑(B0 i) ⊆ (Ss (i + 1)).1 := by
    intro i x hx
    simp only [hB0, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_Icc] at hx
    obtain ⟨j, ⟨hj1, _⟩, rfl⟩ := hx
    exact hain i j hj1
  set d : ℕ → Fin k := fun i => c (insert (a i) (B0 i)) with hd
  obtain ⟨e, he⟩ := Finite.exists_infinite_fiber d
  have hIinf : (d ⁻¹' {e}).Infinite := Set.infinite_coe_iff.mp he
  refine ⟨a '' (d ⁻¹' {e}), ?_, hIinf.image (hainj.injOn), ?_⟩
  · rintro x ⟨i, -, rfl⟩
    exact hmono 0 i (Nat.zero_le _) (hamem i)
  · -- homogeneity
    have key : ∀ B : Finset ℕ, ↑B ⊆ a '' (d ⁻¹' {e}) → B.card = n + 1 → c B = e := by
      intro B hBsub hBcard
      have hBne : B.Nonempty := Finset.card_pos.mp (by omega)
      set b := B.min' hBne with hb
      have hbB : b ∈ B := B.min'_mem hBne
      obtain ⟨i, hi, hib⟩ := hBsub hbB
      have hAcard : (B.erase b).card = n := by
        rw [Finset.card_erase_of_mem hbB, hBcard]
        omega
      have hAsub : ↑(B.erase b) ⊆ (Ss (i + 1)).1 := by
        intro x hx
        simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff] at hx
        obtain ⟨hxB, hxb⟩ := hx
        obtain ⟨j, hj, rfl⟩ := hBsub hxB
        have hle : b ≤ a j := B.min'_le _ hxB
        have : a i < a j := lt_of_le_of_ne (hib ▸ hle) (fun h => hxb (by rw [← h, hib]))
        exact hain i j (hstrict.lt_iff_lt.mp this)
      have h1 : c B = c (insert (a i) (B.erase b)) := by
        rw [hib, Finset.insert_erase hbB]
      have h2 : c (insert (a i) (B.erase b)) = c (insert (a i) (B0 i)) := by
        have := hFhom (Ss i).1 (Ss i).2 (B.erase b) (B0 i)
          (by rw [hstep i] at hAsub; exact hAsub) hAcard
          (by have := hB0sub i; rw [hstep i] at this; exact this) (hB0card i)
        simpa [ha] using this
      rw [h1, h2]
      exact hi
    intro A B hA hAc hB hBc
    rw [key A hA hAc, key B hB hBc]

/-- **The infinite Ramsey theorem.** For every colouring `c` of the finite subsets of `ℕ`
with `k` colours, every dimension `n` and every infinite `S ⊆ ℕ`, there is an infinite
`H ⊆ S` all of whose `n`-element subsets have the same colour. -/
theorem infinite_ramsey :
    ∀ (n k : ℕ) (c : Finset ℕ → Fin k) (S : Set ℕ), S.Infinite →
      ∃ H ⊆ S, H.Infinite ∧ SetHomog n c H := by
  intro n
  induction n with
  | zero =>
      intro k c S hS
      refine ⟨S, subset_rfl, hS, ?_⟩
      intro A B _ hA _ hB
      rw [Finset.card_eq_zero.mp hA, Finset.card_eq_zero.mp hB]
  | succ n IH =>
      intro k c S hS
      have key : ∀ T : Set ℕ, T.Infinite → ∃ U : Set ℕ, U ⊆ T ∧ U.Infinite ∧
          (∀ x ∈ U, sInf T < x) ∧ SetHomog n (fun A => c (insert (sInf T) A)) U := by
        intro T hT
        have hTinf : (T \ Set.Iic (sInf T)).Infinite := hT.diff (Set.finite_Iic _)
        obtain ⟨U, hUsub, hUinf, hUhom⟩ :=
          IH k (fun A => c (insert (sInf T) A)) _ hTinf
        exact ⟨U, fun x hx => (hUsub hx).1, hUinf,
          fun x hx => not_le.mp (hUsub hx).2, hUhom⟩
      choose F hFsub hFinf hFgt hFhom using key
      exact ramsey_step c F hFsub hFinf hFgt hFhom S hS


/-! ## Part 2: the strengthened finite Ramsey theorem -/



/-- A finite set of natural numbers is *relatively large* when it is nonempty and
its cardinality is at least its least element. -/
def IsLarge (Y : Finset ℕ) : Prop :=
  ∃ y ∈ Y, (∀ z ∈ Y, y ≤ z) ∧ y ≤ Y.card

/-- `Y` is homogeneous for the colouring `c` of `n`-element sets: all `n`-element
subsets of `Y` receive the same colour. -/
def IsHomog (n : ℕ) {k : ℕ} (c : Finset ℕ → Fin k) (Y : Finset ℕ) : Prop :=
  ∀ A ∈ Y.powersetCard n, ∀ B ∈ Y.powersetCard n, c A = c B

/-- **The strengthened finite Ramsey theorem of Paris and Harrington.**

For all `n`, `k`, `m` there is an `N` such that every colouring `c` of the
`n`-element subsets of `{1, …, N}` by `k` colours admits a *relatively large*
homogeneous set `Y ⊆ {1, …, N}` with at least `m` elements. -/
theorem Paris_Harrington (n k m : ℕ) :
    ∃ N : ℕ, ∀ c : Finset ℕ → Fin k,
      ∃ Y ⊆ Finset.Icc 1 N, m ≤ Y.card ∧ IsLarge Y ∧ IsHomog n c Y := by
  classical
  by_contra hcon
  have hbad : ∀ N : ℕ, ∃ c : Finset ℕ → Fin k, ∀ Y : Finset ℕ, Y ⊆ Finset.Icc 1 N →
      m ≤ Y.card → IsLarge Y → ¬ IsHomog n c Y := by
    intro N
    by_contra hN
    push_neg at hN
    exact hcon ⟨N, fun c => by
      obtain ⟨Y, hY1, hY2, hY3, hY4⟩ := hN c
      exact ⟨Y, hY1, hY2, hY3, hY4⟩⟩
  choose C hC using hbad
  -- With no colours at all there is nothing to do: no colouring exists.
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; exact (C 0 ∅).elim0
  have : NeBot (atTop : Filter ℕ) := atTop_neBot
  set U : Ultrafilter ℕ := Ultrafilter.of (atTop : Filter ℕ) with hU
  -- the ultrafilter limit colouring
  have hcolex : ∀ A : Finset ℕ, ∃ e : Fin k, ∀ᶠ N in (U : Filter ℕ), C N A = e := by
    intro A
    exact Ultrafilter.eventually_exists_iff.mp (Filter.Eventually.of_forall fun N => ⟨C N A, rfl⟩)
  choose col hcol using hcolex
  -- infinite Ramsey for the limit colouring, inside the positive integers
  have hposinf : ({x : ℕ | 1 ≤ x}).Infinite := by
    apply Set.infinite_of_not_bddAbove
    rintro ⟨b, hb⟩
    exact absurd (hb (show b + 1 ∈ {x : ℕ | 1 ≤ x} from Nat.succ_le_succ (Nat.zero_le b)))
      (by omega)
  obtain ⟨H, hHsub, hHinf, hHhom⟩ := infinite_ramsey n k col _ hposinf
  set a : ℕ := sInf H with hadef
  have haH : a ∈ H := Nat.sInf_mem hHinf.nonempty
  have hamin : ∀ z ∈ H, a ≤ z := fun z hz => Nat.sInf_le hz
  obtain ⟨Y', hY'sub, hY'card⟩ := hHinf.exists_subset_card_eq (max m a)
  set Y : Finset ℕ := insert a Y' with hYdef
  have hYsub : ↑Y ⊆ H := by
    rw [hYdef]
    intro x hx
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
    rcases hx with rfl | hx
    · exact haH
    · exact hY'sub hx
  have hYcard : max m a ≤ Y.card := by
    have : Y'.card ≤ Y.card := Finset.card_le_card (Finset.subset_insert _ _)
    omega
  have haY : a ∈ Y := Finset.mem_insert_self _ _
  have hYne : Y.Nonempty := ⟨a, haY⟩
  have hYpos : ∀ x ∈ Y, 1 ≤ x := fun x hx => hHsub (hYsub hx)
  have hYlarge : IsLarge Y := ⟨a, haY, fun z hz => hamin z (hYsub hz), le_trans (le_max_right m a) hYcard⟩
  set N₀ : ℕ := Y.max' hYne with hN₀
  -- pick a stage `N ≥ N₀` at which the bad colouring `C N` agrees with `col` on `Y`
  have h1 : ∀ᶠ N in (U : Filter ℕ), ∀ A ∈ Y.powersetCard n, C N A = col A :=
    (Filter.eventually_all_finset _).2 fun A _ => hcol A
  have h2 : ∀ᶠ N in (U : Filter ℕ), N₀ ≤ N :=
    Ultrafilter.of_le (atTop : Filter ℕ) (Filter.eventually_ge_atTop N₀)
  obtain ⟨N, hNagree, hNge⟩ := (h1.and h2).exists
  refine hC N Y ?_ ?_ hYlarge ?_
  · intro x hx
    simp only [Finset.mem_Icc]
    exact ⟨hYpos x hx, le_trans (Y.le_max' x hx) hNge⟩
  · exact le_trans (le_max_left m a) hYcard
  · intro A hA B hB
    have hAc : ↑A ⊆ H := by
      have := (Finset.mem_powersetCard.mp hA).1
      exact fun x hx => hYsub (this hx)
    have hBc : ↑B ⊆ H := by
      have := (Finset.mem_powersetCard.mp hB).1
      exact fun x hx => hYsub (this hx)
    rw [hNagree A hA, hNagree B hB]
    exact hHhom A B hAc (Finset.mem_powersetCard.mp hA).2 hBc (Finset.mem_powersetCard.mp hB).2

/-! ### Sanity checks

Relative largeness is a genuine restriction: a set can be homogeneous and big
without being relatively large. -/

example : ¬ IsLarge ({5} : Finset ℕ) := by unfold IsLarge; decide

example : IsLarge ({2, 3} : Finset ℕ) := by unfold IsLarge; decide

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

