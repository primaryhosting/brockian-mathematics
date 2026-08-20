/-!
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Statement: A k-uniform intersecting family on [n] (n≥2k) has size ≤ C(n−1,k−1) (Erdős–Ko–Rado).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Statement: A k-uniform intersecting family on [n] (n≥2k) has size ≤ C(n−1,k−1) (Erdős–Ko–Rado).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Statement: A k-uniform intersecting family on [n] (n≥2k) has size ≤ C(n−1,k−1) (Erdős–Ko–Rado).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

namespace Math2

/-- Transfer a set of naturals to a subset of `Fin n`. -/
def toFinSet (n : ℕ) (A : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ A)

lemma mem_toFinSet {n : ℕ} {A : Finset ℕ} {i : Fin n} :
    i ∈ toFinSet n A ↔ (i : ℕ) ∈ A := by
  simp [toFinSet]

lemma card_toFinSet {n : ℕ} {A : Finset ℕ} (h : A ⊆ Finset.range n) :
    (toFinSet n A).card = A.card := by
  apply Finset.card_bij (fun (i : Fin n) _ => (i : ℕ))
  · intro i hi
    exact mem_toFinSet.1 hi
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro a ha
    have han : a < n := Finset.mem_range.1 (h ha)
    exact ⟨⟨a, han⟩, mem_toFinSet.2 ha, rfl⟩

lemma toFinSet_injOn {n : ℕ} {F : Finset (Finset ℕ)}
    (hsub : ∀ A ∈ F, A ⊆ Finset.range n) :
    Set.InjOn (toFinSet n) F := by
  intro A hA B hB hAB
  ext a
  constructor
  · intro ha
    have han : a < n := Finset.mem_range.1 (hsub A hA ha)
    have : (⟨a, han⟩ : Fin n) ∈ toFinSet n A := mem_toFinSet.2 ha
    rw [hAB] at this
    exact mem_toFinSet.1 this
  · intro ha
    have han : a < n := Finset.mem_range.1 (hsub B hB ha)
    have : (⟨a, han⟩ : Fin n) ∈ toFinSet n B := mem_toFinSet.2 ha
    rw [← hAB] at this
    exact mem_toFinSet.1 this

/-- **Erdős–Ko–Rado theorem.** A `k`-uniform intersecting family of subsets of
`{0, …, n-1}` with `2 * k ≤ n` has at most `(n - 1).choose (k - 1)` members. -/
theorem erdos_ko_rado {n k : ℕ} (F : Finset (Finset ℕ))
    (hsub : ∀ A ∈ F, A ⊆ Finset.range n)
    (hcard : ∀ A ∈ F, A.card = k)
    (hint : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty)
    (hn : 2 * k ≤ n) :
    F.card ≤ (n - 1).choose (k - 1) := by
  classical
  set 𝒜 : Finset (Finset (Fin n)) := F.image (toFinSet n) with h𝒜def
  have hcardeq : 𝒜.card = F.card :=
    Finset.card_image_of_injOn (toFinSet_injOn hsub)
  have hsized : (𝒜 : Set (Finset (Fin n))).Sized k := by
    intro A hA
    simp only [h𝒜def, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hA
    obtain ⟨B, hB, rfl⟩ := hA
    rw [card_toFinSet (hsub B hB)]
    exact hcard B hB
  have hinter : (𝒜 : Set (Finset (Fin n))).Intersecting := by
    intro A hA B hB hdisj
    simp only [h𝒜def, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hA hB
    obtain ⟨A', hA', rfl⟩ := hA
    obtain ⟨B', hB', rfl⟩ := hB
    obtain ⟨x, hx⟩ := hint A' hA' B' hB'
    rw [Finset.mem_inter] at hx
    have hxn : x < n := Finset.mem_range.1 (hsub A' hA' hx.1)
    have h1 : (⟨x, hxn⟩ : Fin n) ∈ toFinSet n A' := mem_toFinSet.2 hx.1
    have h2 : (⟨x, hxn⟩ : Fin n) ∈ toFinSet n B' := mem_toFinSet.2 hx.2
    exact (Finset.disjoint_left.1 hdisj h1) h2
  have hk : k ≤ n / 2 := by omega
  have := Finset.erdos_ko_rado hinter hsized hk
  omega

end Math2

