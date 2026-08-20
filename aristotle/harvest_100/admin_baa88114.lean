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

/-- **Erdős–Ko–Rado theorem**: a `k`-uniform intersecting family of subsets of
`[n] ≃ Fin n`, with `n ≥ 2 * k`, has at most `(n - 1).choose (k - 1)` members. -/
theorem erdos_ko_rado {n k : ℕ} (hn : 2 * k ≤ n) (𝒜 : Finset (Finset (Fin n)))
    (huniform : ∀ A ∈ 𝒜, A.card = k)
    (hinter : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, (A ∩ B).Nonempty) :
    𝒜.card ≤ (n - 1).choose (k - 1) := by
  refine Finset.erdos_ko_rado (r := k) ?_ ?_ (by omega)
  · intro A hA B hB hdisj
    obtain ⟨x, hx⟩ := hinter A hA B hB
    rw [Finset.mem_inter] at hx
    exact (Finset.disjoint_left.mp hdisj hx.1) hx.2
  · intro A hA
    exact huniform A hA

/-- Version of the Erdős–Ko–Rado theorem for families of subsets of
`[n] = {0, 1, ..., n-1} = Finset.range n`, viewed inside `ℕ`. -/
theorem erdos_ko_rado_range {n k : ℕ} (hn : 2 * k ≤ n) (𝒜 : Finset (Finset ℕ))
    (hsub : ∀ A ∈ 𝒜, A ⊆ Finset.range n)
    (huniform : ∀ A ∈ 𝒜, A.card = k)
    (hinter : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, (A ∩ B).Nonempty) :
    𝒜.card ≤ (n - 1).choose (k - 1) := by
  classical
  set f : Finset ℕ → Finset (Fin n) :=
    fun A => Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ A) with hf
  have hmem : ∀ (A : Finset ℕ) (i : Fin n), i ∈ f A ↔ (i : ℕ) ∈ A := by
    intro A i; simp [hf]
  have hcard : ∀ A ∈ 𝒜, (f A).card = A.card := by
    intro A hA
    have himg : (f A).image (Fin.val) = A := by
      ext x
      simp only [Finset.mem_image, hf, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact hi
      · intro hx
        have : x < n := Finset.mem_range.mp (hsub A hA hx)
        exact ⟨⟨x, this⟩, hx, rfl⟩
    calc (f A).card = ((f A).image Fin.val).card :=
          (Finset.card_image_of_injective _ Fin.val_injective).symm
      _ = A.card := by rw [himg]
  have hinj : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, f A = f B → A = B := by
    intro A hA B hB hAB
    ext x
    constructor
    · intro hx
      have hxn : x < n := Finset.mem_range.mp (hsub A hA hx)
      have := (hmem A ⟨x, hxn⟩).mpr hx
      rw [hAB] at this
      exact (hmem B ⟨x, hxn⟩).mp this
    · intro hx
      have hxn : x < n := Finset.mem_range.mp (hsub B hB hx)
      have := (hmem B ⟨x, hxn⟩).mpr hx
      rw [← hAB] at this
      exact (hmem A ⟨x, hxn⟩).mp this
  have hcard𝒜 : (𝒜.image f).card = 𝒜.card :=
    Finset.card_image_of_injOn (fun A hA B hB h => hinj A hA B hB h)
  rw [← hcard𝒜]
  refine Math2.erdos_ko_rado hn (𝒜.image f) ?_ ?_
  · intro C hC
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hC
    rw [hcard A hA]; exact huniform A hA
  · intro C hC D hD
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨x, hx⟩ := hinter A hA B hB
    rw [Finset.mem_inter] at hx
    have hxn : x < n := Finset.mem_range.mp (hsub A hA hx.1)
    exact ⟨⟨x, hxn⟩, Finset.mem_inter.mpr ⟨(hmem A ⟨x, hxn⟩).mpr hx.1,
      (hmem B ⟨x, hxn⟩).mpr hx.2⟩⟩

end Math2

