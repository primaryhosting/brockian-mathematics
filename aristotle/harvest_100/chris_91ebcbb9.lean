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

/-- Encoding of a set of naturals as a subset of `Fin n`. -/
private def toFinSet (n : ℕ) (A : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ A)

private lemma mem_toFinSet {n : ℕ} {A : Finset ℕ} {i : Fin n} :
    i ∈ toFinSet n A ↔ (i : ℕ) ∈ A := by
  simp [toFinSet]

private lemma image_val_toFinSet {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range n) :
    (toFinSet n A).image (Fin.val) = A := by
  ext x
  simp only [Finset.mem_image, mem_toFinSet]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact hi
  · intro hx
    have hxn : x < n := Finset.mem_range.mp (hA hx)
    exact ⟨⟨x, hxn⟩, hx, rfl⟩

private lemma card_toFinSet {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range n) :
    (toFinSet n A).card = A.card := by
  have h := Finset.card_image_of_injective (toFinSet n A) Fin.val_injective
  rw [image_val_toFinSet hA] at h
  exact h.symm

/-- **Erdős–Ko–Rado theorem**. A `k`-uniform intersecting family of subsets of
`{0, 1, …, n-1}` with `n ≥ 2k` has at most `(n-1).choose (k-1)` members. -/
theorem erdos_ko_rado {n k : ℕ} {F : Finset (Finset ℕ)}
    (hsub : ∀ A ∈ F, A ⊆ Finset.range n)
    (hcard : ∀ A ∈ F, A.card = k)
    (hint : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty)
    (hn : 2 * k ≤ n) :
    F.card ≤ (n - 1).choose (k - 1) := by
  classical
  set 𝒜 : Finset (Finset (Fin n)) := F.image (toFinSet n) with h𝒜def
  have hcard_eq : 𝒜.card = F.card := by
    refine Finset.card_image_of_injOn ?_
    intro A hA B hB hAB
    rw [← image_val_toFinSet (hsub A hA), ← image_val_toFinSet (hsub B hB), hAB]
  have hmem : ∀ s ∈ 𝒜, ∃ A ∈ F, toFinSet n A = s := by
    intro s hs
    simpa [h𝒜def, eq_comm] using Finset.mem_image.mp hs
  have hsized : (𝒜 : Set (Finset (Fin n))).Sized k := by
    intro s hs
    obtain ⟨A, hA, rfl⟩ := hmem s (by simpa using hs)
    rw [card_toFinSet (hsub A hA), hcard A hA]
  have hinter : (𝒜 : Set (Finset (Fin n))).Intersecting := by
    intro s hs t ht hdisj
    obtain ⟨A, hA, rfl⟩ := hmem s (by simpa using hs)
    obtain ⟨B, hB, rfl⟩ := hmem t (by simpa using ht)
    obtain ⟨x, hx⟩ := hint A hA B hB
    rw [Finset.mem_inter] at hx
    have hxn : x < n := Finset.mem_range.mp (hsub A hA hx.1)
    have h1 : (⟨x, hxn⟩ : Fin n) ∈ toFinSet n A := mem_toFinSet.mpr hx.1
    have h2 : (⟨x, hxn⟩ : Fin n) ∈ toFinSet n B := mem_toFinSet.mpr hx.2
    exact (Finset.disjoint_left.mp hdisj h1) h2
  have hhalf : k ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    omega
  have := Finset.erdos_ko_rado hinter hsized hhalf
  rw [hcard_eq] at this
  simpa using this

end Math2

