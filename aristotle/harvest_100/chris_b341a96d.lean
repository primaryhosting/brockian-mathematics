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

set_option grind.warning false

namespace Math2

open Finset

/-- Transfer of a set of naturals contained in `[n] = range n` to a `Finset (Fin n)`. -/
private def toFin (n : ℕ) (A : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ A)

private lemma image_val_toFin {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range n) :
    (toFin n A).image (Fin.val) = A := by
  ext x
  simp only [toFin, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact hi
  · intro hx
    have hxn : x < n := Finset.mem_range.mp (hA hx)
    exact ⟨⟨x, hxn⟩, hx, rfl⟩

private lemma card_toFin {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range n) :
    (toFin n A).card = A.card := by
  conv_rhs => rw [← image_val_toFin hA]
  rw [Finset.card_image_of_injective _ Fin.val_injective]

/-- **Erdős–Ko–Rado theorem**: a `k`-uniform intersecting family of subsets of
`[n] = {0, …, n-1}` with `n ≥ 2k` has at most `C(n-1, k-1)` members.

This is derived from Mathlib's `Finset.erdos_ko_rado` (proved there via the
Kruskal–Katona theorem), transported from `Fin n` to subsets of `Finset.range n`. -/
theorem erdos_ko_rado {n k : ℕ} (𝒜 : Finset (Finset ℕ))
    (hsub : ∀ A ∈ 𝒜, A ⊆ Finset.range n)
    (hsize : ∀ A ∈ 𝒜, A.card = k)
    (hinter : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, (A ∩ B).Nonempty)
    (hn : 2 * k ≤ n) :
    𝒜.card ≤ (n - 1).choose (k - 1) := by
  classical
  set ℬ : Finset (Finset (Fin n)) := 𝒜.image (toFin n) with hℬ
  have hcard : ℬ.card = 𝒜.card := by
    refine Finset.card_image_of_injOn ?_
    intro A hA B hB hAB
    rw [← image_val_toFin (hsub A hA), ← image_val_toFin (hsub B hB), hAB]
  have hsized : Set.Sized k (↑ℬ : Set (Finset (Fin n))) := by
    intro s hs
    simp only [hℬ, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hs
    obtain ⟨A, hA, rfl⟩ := hs
    rw [card_toFin (hsub A hA), hsize A hA]
  have hint : (↑ℬ : Set (Finset (Fin n))).Intersecting := by
    intro s hs t ht
    simp only [hℬ, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hs ht
    obtain ⟨A, hA, rfl⟩ := hs
    obtain ⟨B, hB, rfl⟩ := ht
    obtain ⟨x, hx⟩ := hinter A hA B hB
    rw [Finset.mem_inter] at hx
    have hxn : x < n := Finset.mem_range.mp (hsub A hA hx.1)
    intro hdisj
    have : (⟨x, hxn⟩ : Fin n) ∈ toFin n A ∩ toFin n B := by
      simp [toFin, hx.1, hx.2]
    rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj] at this
    exact absurd this (Finset.notMem_empty _)
  have hk : k ≤ n / 2 := by omega
  have := Finset.erdos_ko_rado hint hsized hk
  rwa [hcard] at this

end Math2

