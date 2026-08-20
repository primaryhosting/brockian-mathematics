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

/-- The transfer map sending a set of naturals to the corresponding subset of `Fin n`. -/
private def toFin (n : ℕ) (A : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i : Fin n => (i : ℕ) ∈ A

private lemma mem_toFin {n : ℕ} {A : Finset ℕ} {i : Fin n} :
    i ∈ toFin n A ↔ (i : ℕ) ∈ A := by
  simp [toFin]

private lemma card_toFin {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range n) :
    (toFin n A).card = A.card := by
  have h : ∀ m ∈ A, m < n := fun m hm => Finset.mem_range.mp (hA hm)
  have : toFin n A = A.attachFin h := by
    ext i
    simp [mem_toFin, Finset.mem_attachFin]
  rw [this, Finset.card_attachFin]

/-- **Erdős–Ko–Rado theorem.**  A `k`-uniform intersecting family of subsets of
`{0, 1, …, n-1}` with `2 * k ≤ n` has at most `(n - 1).choose (k - 1)` members.

The proof transfers the statement to `Fin n` and invokes Mathlib's
`Finset.erdos_ko_rado` (proved there via the Kruskal–Katona theorem). -/
theorem erdos_ko_rado {n k : ℕ} {F : Finset (Finset ℕ)}
    (hsub : ∀ A ∈ F, A ⊆ Finset.range n)
    (hsize : ∀ A ∈ F, A.card = k)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty)
    (hn : 2 * k ≤ n) :
    F.card ≤ (n - 1).choose (k - 1) := by
  classical
  set 𝒜 : Finset (Finset (Fin n)) := F.image (toFin n) with h𝒜
  -- `toFin n` is injective on `F`
  have hinj : ∀ A ∈ F, ∀ B ∈ F, toFin n A = toFin n B → A = B := by
    intro A hA B hB hAB
    ext m
    constructor
    · intro hm
      have hmn : m < n := Finset.mem_range.mp (hsub A hA hm)
      have : (⟨m, hmn⟩ : Fin n) ∈ toFin n A := mem_toFin.mpr hm
      rw [hAB] at this
      exact mem_toFin.mp this
    · intro hm
      have hmn : m < n := Finset.mem_range.mp (hsub B hB hm)
      have : (⟨m, hmn⟩ : Fin n) ∈ toFin n B := mem_toFin.mpr hm
      rw [← hAB] at this
      exact mem_toFin.mp this
  have hcard : 𝒜.card = F.card := Finset.card_image_of_injOn hinj
  have hSized : (𝒜 : Set (Finset (Fin n))).Sized k := by
    intro S hS
    simp only [h𝒜, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hS
    obtain ⟨A, hA, rfl⟩ := hS
    rw [card_toFin (hsub A hA), hsize A hA]
  have hInt : (𝒜 : Set (Finset (Fin n))).Intersecting := by
    intro S hS T hT hdisj
    simp only [h𝒜, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hS hT
    obtain ⟨A, hA, rfl⟩ := hS
    obtain ⟨B, hB, rfl⟩ := hT
    obtain ⟨m, hm⟩ := hinter A hA B hB
    rw [Finset.mem_inter] at hm
    have hmn : m < n := Finset.mem_range.mp (hsub A hA hm.1)
    have h1 : (⟨m, hmn⟩ : Fin n) ∈ toFin n A := mem_toFin.mpr hm.1
    have h2 : (⟨m, hmn⟩ : Fin n) ∈ toFin n B := mem_toFin.mpr hm.2
    exact (Finset.disjoint_left.mp hdisj h1) h2
  have hk : k ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    omega
  have := Finset.erdos_ko_rado hInt hSized hk
  rwa [hcard] at this

end Math2

