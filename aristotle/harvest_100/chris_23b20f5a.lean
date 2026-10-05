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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

/-- Transfer a set of naturals to the corresponding subset of `Fin n`. -/
private def toFin (n : ℕ) (A : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ A)

private lemma image_val_toFin {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range n) :
    (toFin n A).image (Fin.val) = A := by
  ext m
  simp only [toFin, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hm
    have hmn : m < n := Finset.mem_range.mp (hA hm)
    exact ⟨⟨m, hmn⟩, hm, rfl⟩

private lemma card_toFin {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range n) :
    (toFin n A).card = A.card := by
  have h := Finset.card_image_of_injective (toFin n A) Fin.val_injective
  rw [image_val_toFin hA] at h
  exact h.symm

/-- **Erdős–Ko–Rado theorem.** If `𝒜` is a family of `k`-element subsets of
`{0, 1, ..., n-1}` such that any two members of `𝒜` intersect, and `n ≥ 2k`,
then `𝒜` has at most `C(n-1, k-1)` members. -/
theorem erdos_ko_rado {n k : ℕ} (𝒜 : Finset (Finset ℕ))
    (hsub : ∀ A ∈ 𝒜, A ⊆ Finset.range n)
    (hcard : ∀ A ∈ 𝒜, A.card = k)
    (hint : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, (A ∩ B).Nonempty)
    (hn : 2 * k ≤ n) :
    𝒜.card ≤ (n - 1).choose (k - 1) := by
  classical
  set ℬ : Finset (Finset (Fin n)) := 𝒜.image (toFin n) with hℬ
  have hinj : Set.InjOn (toFin n) (𝒜 : Set (Finset ℕ)) := by
    intro A hA B hB hAB
    have := image_val_toFin (hsub A hA)
    rw [hAB, image_val_toFin (hsub B hB)] at this
    exact this.symm
  have hcards : 𝒜.card = ℬ.card := (Finset.card_image_of_injOn hinj).symm
  have hsized : Set.Sized k (ℬ : Set (Finset (Fin n))) := by
    intro s hs
    simp only [hℬ, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hs
    obtain ⟨A, hA, rfl⟩ := hs
    rw [card_toFin (hsub A hA), hcard A hA]
  have hinter : (ℬ : Set (Finset (Fin n))).Intersecting := by
    intro s hs t ht hdisj
    simp only [hℬ, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hs ht
    obtain ⟨A, hA, rfl⟩ := hs
    obtain ⟨B, hB, rfl⟩ := ht
    obtain ⟨x, hx⟩ := hint A hA B hB
    rw [Finset.mem_inter] at hx
    have hxn : x < n := Finset.mem_range.mp (hsub A hA hx.1)
    have hmem : (⟨x, hxn⟩ : Fin n) ∈ toFin n A ⊓ toFin n B := by
      simp only [Finset.inf_eq_inter, Finset.mem_inter, toFin, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨hx.1, hx.2⟩
    rw [disjoint_iff] at hdisj
    rw [hdisj] at hmem
    simp at hmem
  have hkn : k ≤ n / 2 := by omega
  rw [hcards]
  exact Finset.erdos_ko_rado hinter hsized hkn

end Math2

