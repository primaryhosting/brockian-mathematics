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

open Finset

namespace Math2

/-- Transfer a set of naturals to a set of elements of `Fin n`. -/
private def toFin (n : ℕ) (A : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ A)

private lemma mem_toFin {n : ℕ} {A : Finset ℕ} {i : Fin n} :
    i ∈ toFin n A ↔ (i : ℕ) ∈ A := by
  simp [toFin]

private lemma card_toFin {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range n) :
    (toFin n A).card = A.card := by
  refine Finset.card_bij (fun i _ => (i : ℕ)) (fun i hi => mem_toFin.1 hi) ?_ ?_
  · intro i _ j _ h
    exact Fin.ext h
  · intro b hb
    have hbn : b < n := Finset.mem_range.1 (hA hb)
    exact ⟨⟨b, hbn⟩, mem_toFin.2 hb, rfl⟩

private lemma toFin_injOn {n : ℕ} {F : Finset (Finset ℕ)}
    (hF : ∀ A ∈ F, A ⊆ Finset.range n) :
    Set.InjOn (toFin n) (F : Set (Finset ℕ)) := by
  intro A hA B hB h
  ext m
  constructor
  · intro hm
    have hmn : m < n := Finset.mem_range.1 (hF A hA hm)
    have : (⟨m, hmn⟩ : Fin n) ∈ toFin n A := mem_toFin.2 hm
    rw [h] at this
    exact mem_toFin.1 this
  · intro hm
    have hmn : m < n := Finset.mem_range.1 (hF B hB hm)
    have : (⟨m, hmn⟩ : Fin n) ∈ toFin n B := mem_toFin.2 hm
    rw [← h] at this
    exact mem_toFin.1 this

/-- **Erdős–Ko–Rado theorem**: a `k`-uniform intersecting family of subsets of
`[n] = {0, 1, ..., n-1}` with `n ≥ 2k` has at most `(n-1).choose (k-1)` members.

This is a restatement, for families of subsets of `Finset.range n`, of Mathlib's
`Finset.erdos_ko_rado` (proved there via the Kruskal–Katona theorem). -/
theorem erdos_ko_rado {n k : ℕ} {F : Finset (Finset ℕ)}
    (hsub : ∀ A ∈ F, A ⊆ Finset.range n)
    (hcard : ∀ A ∈ F, A.card = k)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty)
    (hn : 2 * k ≤ n) :
    F.card ≤ (n - 1).choose (k - 1) := by
  classical
  set 𝒜 : Finset (Finset (Fin n)) := F.image (toFin n) with h𝒜
  have hcard𝒜 : 𝒜.card = F.card := Finset.card_image_of_injOn (toFin_injOn hsub)
  have hint : (𝒜 : Set (Finset (Fin n))).Intersecting := by
    intro A hA B hB hdisj
    simp only [h𝒜, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hA hB
    obtain ⟨A', hA', rfl⟩ := hA
    obtain ⟨B', hB', rfl⟩ := hB
    obtain ⟨m, hm⟩ := hinter A' hA' B' hB'
    rw [Finset.mem_inter] at hm
    have hmn : m < n := Finset.mem_range.1 (hsub A' hA' hm.1)
    have h1 : (⟨m, hmn⟩ : Fin n) ∈ toFin n A' := mem_toFin.2 hm.1
    have h2 : (⟨m, hmn⟩ : Fin n) ∈ toFin n B' := mem_toFin.2 hm.2
    exact (Finset.disjoint_left.1 hdisj h1) h2
  have hsized : (𝒜 : Set (Finset (Fin n))).Sized k := by
    intro A hA
    simp only [h𝒜, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hA
    obtain ⟨A', hA', rfl⟩ := hA
    rw [card_toFin (hsub A' hA'), hcard A' hA']
  have hk : k ≤ n / 2 := by omega
  have := Finset.erdos_ko_rado hint hsized hk
  rwa [hcard𝒜] at this

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

