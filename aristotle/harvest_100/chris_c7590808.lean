/-
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Math2

open Finset

/-- The canonical map sending a set of naturals to the corresponding set of elements of
`Fin n`, keeping exactly the elements that are `< n`. -/
def toFinSet (n : ℕ) (A : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i : Fin n => (i : ℕ) ∈ A

lemma mem_toFinSet {n : ℕ} {A : Finset ℕ} {i : Fin n} :
    i ∈ toFinSet n A ↔ (i : ℕ) ∈ A := by
  simp [toFinSet]

lemma image_val_toFinSet {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range n) :
    (toFinSet n A).image (Fin.val) = A := by
  ext x
  simp only [Finset.mem_image, mem_toFinSet]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact hi
  · intro hx
    have hxn : x < n := Finset.mem_range.mp (hA hx)
    exact ⟨⟨x, hxn⟩, hx, rfl⟩

lemma card_toFinSet {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range n) :
    (toFinSet n A).card = A.card := by
  have h : ((toFinSet n A).image Fin.val).card = (toFinSet n A).card :=
    Finset.card_image_of_injective _ Fin.val_injective
  rw [image_val_toFinSet hA] at h
  exact h.symm

/-- **Erdős–Ko–Rado theorem.**  A family `𝒜` of `k`-element subsets of `[n] = {0, …, n-1}`
in which any two members intersect has at most `(n-1).choose (k-1)` members,
provided `n ≥ 2 * k`. -/
theorem erdos_ko_rado {n k : ℕ} (hn : 2 * k ≤ n) (𝒜 : Finset (Finset ℕ))
    (hsub : ∀ A ∈ 𝒜, A ⊆ Finset.range n)
    (hcard : ∀ A ∈ 𝒜, A.card = k)
    (hint : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, (A ∩ B).Nonempty) :
    𝒜.card ≤ (n - 1).choose (k - 1) := by
  classical
  set ℬ : Finset (Finset (Fin n)) := 𝒜.image (toFinSet n) with hB
  have hinj : Set.InjOn (toFinSet n) 𝒜 := by
    intro A hA B hBmem h
    rw [← image_val_toFinSet (hsub A hA), ← image_val_toFinSet (hsub B hBmem), h]
  have hcardB : ℬ.card = 𝒜.card := Finset.card_image_of_injOn hinj
  have hsized : (ℬ : Set (Finset (Fin n))).Sized k := by
    intro s hs
    simp only [hB, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hs
    obtain ⟨A, hA, rfl⟩ := hs
    rw [card_toFinSet (hsub A hA), hcard A hA]
  have hinter : (ℬ : Set (Finset (Fin n))).Intersecting := by
    intro s hs t ht hdisj
    simp only [hB, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hs ht
    obtain ⟨A, hA, rfl⟩ := hs
    obtain ⟨B, hBm, rfl⟩ := ht
    obtain ⟨x, hx⟩ := hint A hA B hBm
    rw [Finset.mem_inter] at hx
    have hxn : x < n := Finset.mem_range.mp (hsub A hA hx.1)
    have h1 : (⟨x, hxn⟩ : Fin n) ∈ toFinSet n A := mem_toFinSet.mpr hx.1
    have h2 : (⟨x, hxn⟩ : Fin n) ∈ toFinSet n B := mem_toFinSet.mpr hx.2
    exact (Finset.disjoint_left.mp hdisj h1) h2
  have hk : k ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    omega
  have := Finset.erdos_ko_rado hinter hsized hk
  rw [hcardB] at this
  exact this

/-! ## Sharpness of the bound

The bound is attained by the *star*: the family of all `k`-element subsets of `[n]`
containing the fixed element `0`. -/

/-- The star family: all `k`-element subsets of `[n]` containing the element `0`. -/
def star (n k : ℕ) : Finset (Finset ℕ) :=
  ((Finset.range n).powersetCard k).filter fun A => 0 ∈ A

lemma mem_star {n k : ℕ} {A : Finset ℕ} :
    A ∈ star n k ↔ (A ⊆ Finset.range n ∧ A.card = k) ∧ 0 ∈ A := by
  simp [star, Finset.mem_powersetCard]

lemma card_star {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) : (star n k).card = (n - 1).choose (k - 1) := by
  classical
  have hcard : (((Finset.range n).erase 0).powersetCard (k - 1)).card = (n - 1).choose (k - 1) := by
    rw [Finset.card_powersetCard, Finset.card_erase_of_mem (by simpa using hn), Finset.card_range]
  rw [star, ← hcard]
  apply Finset.card_bij' (fun A _ => A.erase 0) (fun B _ => insert 0 B)
  · intro A hA
    simp only [Finset.mem_filter] at hA
    exact Finset.insert_erase hA.2
  · intro B hB
    rw [Finset.mem_powersetCard] at hB
    have h0B : 0 ∉ B := fun h => (Finset.notMem_erase 0 _) (hB.1 h)
    exact Finset.erase_insert h0B
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hA
    obtain ⟨⟨hsub, hc⟩, h0⟩ := hA
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.erase_subset_erase _ hsub, ?_⟩
    rw [Finset.card_erase_of_mem h0, hc]
  · intro B hB
    rw [Finset.mem_powersetCard] at hB
    obtain ⟨hsub, hc⟩ := hB
    have h0B : 0 ∉ B := fun h => (Finset.notMem_erase 0 _) (hsub h)
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self _ _⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simpa using hn
      · exact Finset.mem_of_mem_erase (hsub hx)
    · rw [Finset.card_insert_of_notMem h0B, hc]; omega

/-- **The Erdős–Ko–Rado bound is sharp.**  For `1 ≤ k` and `2 * k ≤ n` there is a `k`-uniform
intersecting family of subsets of `[n]` of size exactly `(n - 1).choose (k - 1)`, namely the
family of all `k`-subsets containing `0`. -/
theorem erdos_ko_rado_sharp {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    ∃ 𝒜 : Finset (Finset ℕ),
      (∀ A ∈ 𝒜, A ⊆ Finset.range n) ∧ (∀ A ∈ 𝒜, A.card = k) ∧
      (∀ A ∈ 𝒜, ∀ B ∈ 𝒜, (A ∩ B).Nonempty) ∧ 𝒜.card = (n - 1).choose (k - 1) := by
  have hn1 : 1 ≤ n := by omega
  refine ⟨star n k, ?_, ?_, ?_, card_star hn1 hk⟩
  · exact fun A hA => (mem_star.mp hA).1.1
  · exact fun A hA => (mem_star.mp hA).1.2
  · intro A hA B hB
    exact ⟨0, Finset.mem_inter.mpr ⟨(mem_star.mp hA).2, (mem_star.mp hB).2⟩⟩

end Math2

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

