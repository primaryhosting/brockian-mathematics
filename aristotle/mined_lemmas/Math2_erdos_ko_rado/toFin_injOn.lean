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
