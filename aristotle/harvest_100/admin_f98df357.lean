import Mathlib

/-!
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
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

namespace Math2

/-- Transfer of a subset of `[n] = Finset.range n` (viewed inside `ℕ`) to a subset of
`Fin n`. -/
noncomputable def toFinSet (n : ℕ) (A : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i : Fin n => (i : ℕ) ∈ A

lemma mem_toFinSet {n : ℕ} {A : Finset ℕ} {i : Fin n} :
    i ∈ toFinSet n A ↔ (i : ℕ) ∈ A := by
  simp [toFinSet]

/-- On subsets of `[n]`, the transfer map preserves cardinality. -/
lemma card_toFinSet {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range n) :
    (toFinSet n A).card = A.card := by
  classical
  have : (toFinSet n A).image (fun i : Fin n => (i : ℕ)) = A := by
    ext a
    simp only [Finset.mem_image, mem_toFinSet]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro ha
      exact ⟨⟨a, Finset.mem_range.mp (hA ha)⟩, ha, rfl⟩
  calc (toFinSet n A).card
      = ((toFinSet n A).image (fun i : Fin n => (i : ℕ))).card := by
        refine (Finset.card_image_of_injective _ ?_).symm
        exact Fin.val_injective
    _ = A.card := by rw [this]

/-- The transfer map is injective on subsets of `[n]`. -/
lemma toFinSet_injOn {n : ℕ} {A B : Finset ℕ} (hA : A ⊆ Finset.range n)
    (hB : B ⊆ Finset.range n) (h : toFinSet n A = toFinSet n B) : A = B := by
  ext a
  constructor
  · intro ha
    have han : a < n := Finset.mem_range.mp (hA ha)
    have : (⟨a, han⟩ : Fin n) ∈ toFinSet n A := mem_toFinSet.mpr ha
    rw [h] at this
    exact mem_toFinSet.mp this
  · intro ha
    have han : a < n := Finset.mem_range.mp (hB ha)
    have : (⟨a, han⟩ : Fin n) ∈ toFinSet n B := mem_toFinSet.mpr ha
    rw [← h] at this
    exact mem_toFinSet.mp this

/-- **Erdős–Ko–Rado theorem.**

If `𝒜` is a family of `k`-element subsets of `[n] = {0, 1, ..., n - 1}` with `n ≥ 2 * k`, and any
two members of `𝒜` intersect, then `𝒜` has at most `(n - 1).choose (k - 1)` members. -/
theorem erdos_ko_rado {n k : ℕ} (hn : 2 * k ≤ n) (𝒜 : Finset (Finset ℕ))
    (hsub : ∀ A ∈ 𝒜, A ⊆ Finset.range n)
    (hcard : ∀ A ∈ 𝒜, A.card = k)
    (hint : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, (A ∩ B).Nonempty) :
    𝒜.card ≤ (n - 1).choose (k - 1) := by
  classical
  set ℬ : Finset (Finset (Fin n)) := 𝒜.image (toFinSet n) with hℬ
  have hcardB : ℬ.card = 𝒜.card := by
    refine Finset.card_image_of_injOn ?_
    intro A hA B hB h
    exact toFinSet_injOn (hsub A hA) (hsub B hB) h
  have hsized : (ℬ : Set (Finset (Fin n))).Sized k := by
    intro s hs
    simp only [hℬ, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hs
    obtain ⟨A, hA, rfl⟩ := hs
    rw [card_toFinSet (hsub A hA), hcard A hA]
  have hinter : (ℬ : Set (Finset (Fin n))).Intersecting := by
    intro s hs t ht hst
    simp only [hℬ, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hs ht
    obtain ⟨A, hA, rfl⟩ := hs
    obtain ⟨B, hB, rfl⟩ := ht
    obtain ⟨a, ha⟩ := hint A hA B hB
    rw [Finset.mem_inter] at ha
    have han : a < n := Finset.mem_range.mp (hsub A hA ha.1)
    have hmem : (⟨a, han⟩ : Fin n) ∈ toFinSet n A ⊓ toFinSet n B := by
      simp only [Finset.inf_eq_inter, Finset.mem_inter, mem_toFinSet]
      exact ⟨ha.1, ha.2⟩
    exact (Finset.not_nonempty_iff_eq_empty.mpr (Finset.disjoint_iff_inter_eq_empty.mp hst))
      ⟨⟨a, han⟩, by simpa using hmem⟩
  have hkn : k ≤ n / 2 := by omega
  have hEKR := Finset.erdos_ko_rado hinter hsized hkn
  rwa [hcardB] at hEKR

end Math2

