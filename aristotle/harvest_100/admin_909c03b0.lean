import Mathlib

/-!
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

/-- **Erdős–Ko–Rado theorem**: a `k`-uniform intersecting family of subsets of `[n] = Fin n`
with `2 * k ≤ n` has at most `(n - 1).choose (k - 1)` members.

This is obtained from Mathlib's `Finset.erdos_ko_rado`
(`Mathlib/Combinatorics/SetFamily/KruskalKatona.lean`), which is stated using
`Set.Intersecting` and `Set.Sized`. -/
theorem erdos_ko_rado {n k : ℕ} (𝒜 : Finset (Finset (Fin n)))
    (huniform : ∀ A ∈ 𝒜, A.card = k)
    (hinter : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, (A ∩ B).Nonempty)
    (hnk : 2 * k ≤ n) :
    𝒜.card ≤ (n - 1).choose (k - 1) := by
  refine Finset.erdos_ko_rado (r := k) ?_ ?_ ?_
  · intro A hA B hB hd
    exact (Finset.not_disjoint_iff_nonempty_inter.2 (hinter A hA B hB)) hd
  · intro A hA
    exact huniform A hA
  · omega

/-- The image of `A ⊆ [n] = range n` inside `Fin n`. -/
private def restrictFin (n : ℕ) (A : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ A)

private lemma restrictFin_eq_attachFin {n : ℕ} {A : Finset ℕ} (hA : ∀ m ∈ A, m < n) :
    restrictFin n A = A.attachFin hA := by
  ext i
  simp [restrictFin, Finset.mem_attachFin]

private lemma card_restrictFin {n : ℕ} {A : Finset ℕ} (hA : ∀ m ∈ A, m < n) :
    (restrictFin n A).card = A.card := by
  rw [restrictFin_eq_attachFin hA, Finset.card_attachFin]

/-- **Erdős–Ko–Rado theorem**, phrased for families of subsets of `[n] = Finset.range n`. -/
theorem erdos_ko_rado_range {n k : ℕ} (𝒜 : Finset (Finset ℕ))
    (hground : ∀ A ∈ 𝒜, A ⊆ Finset.range n)
    (huniform : ∀ A ∈ 𝒜, A.card = k)
    (hinter : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, (A ∩ B).Nonempty)
    (hnk : 2 * k ≤ n) :
    𝒜.card ≤ (n - 1).choose (k - 1) := by
  have hlt : ∀ A ∈ 𝒜, ∀ m ∈ A, m < n := by
    intro A hA m hm
    simpa using hground A hA hm
  have hinj : Set.InjOn (restrictFin n) 𝒜 := by
    intro A hA B hB hAB
    ext m
    constructor
    · intro hm
      have : (⟨m, hlt A hA m hm⟩ : Fin n) ∈ restrictFin n A := by
        simp [restrictFin, hm]
      rw [hAB] at this
      simpa [restrictFin] using this
    · intro hm
      have : (⟨m, hlt B hB m hm⟩ : Fin n) ∈ restrictFin n B := by
        simp [restrictFin, hm]
      rw [← hAB] at this
      simpa [restrictFin] using this
  rw [← Finset.card_image_of_injOn hinj]
  refine erdos_ko_rado _ ?_ ?_ hnk
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hA
    rw [card_restrictFin (hlt B hB)]
    exact huniform B hB
  · intro A hA B hB
    obtain ⟨A', hA', rfl⟩ := Finset.mem_image.1 hA
    obtain ⟨B', hB', rfl⟩ := Finset.mem_image.1 hB
    obtain ⟨m, hm⟩ := hinter A' hA' B' hB'
    rw [Finset.mem_inter] at hm
    exact ⟨⟨m, hlt A' hA' m hm.1⟩, by simp [restrictFin, hm.1, hm.2]⟩

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

