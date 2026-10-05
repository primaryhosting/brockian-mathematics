/-
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- The number of distinct residue classes modulo `p` occupied by the tuple `H`.
This is the local density `ν_p(H)` appearing in the Hardy–Littlewood singular series. -/

theorem SingularSeriesGaps13501360 :
    (∀ d ∈ Finset.Icc (1350 : ℤ) 1360, IsAdmissible ({0, d} : Finset ℤ) ↔ Even d) ∧
    (Finset.Icc (1350 : ℤ) 1360).filter
        (fun d => IsAdmissible ({0, d} : Finset ℤ)) =
      ({1350, 1352, 1354, 1356, 1358, 1360} : Finset ℤ) ∧
    ((Finset.Icc (1350 : ℤ) 1360).filter
        (fun d => IsAdmissible ({0, d} : Finset ℤ))).card = 6 ∧
    (∀ d ∈ Finset.Icc (1350 : ℤ) 1360, Even d →
      ∀ p : ℕ, p.Prime → 0 < singularFactor p ({0, d} : Finset ℤ)) ∧
    (∀ d ∈ Finset.Icc (1350 : ℤ) 1360, Even d →
      ∀ N : ℕ, 0 < singularSeriesPartial N ({0, d} : Finset ℤ)) := by
  have key : ∀ d ∈ Finset.Icc (1350 : ℤ) 1360,
      (IsAdmissible ({0, d} : Finset ℤ) ↔ Even d) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    exact isAdmissible_pair_iff (by omega)
  have hset : (Finset.Icc (1350 : ℤ) 1360).filter
      (fun d => IsAdmissible ({0, d} : Finset ℤ)) =
      ({1350, 1352, 1354, 1356, 1358, 1360} : Finset ℤ) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hd, hadm⟩
      have he : Even d := (key d (Finset.mem_Icc.2 hd)).1 hadm
      rw [Int.even_iff] at he
      omega
    · intro h
      have hd : 1350 ≤ d ∧ d ≤ 1360 := by rcases h with h|h|h|h|h|h <;> omega
      refine ⟨hd, (key d (Finset.mem_Icc.2 hd)).2 ?_⟩
      rw [Int.even_iff]
      rcases h with h|h|h|h|h|h <;> omega
  refine ⟨key, hset, ?_, ?_, ?_⟩
  · rw [hset]; decide
  · intro d hd he p hp
    exact singularFactor_pos ((key d hd).2 he) hp
  · intro d hd he N
    exact singularSeriesPartial_pos ((key d hd).2 he) N

/-- Concrete instance: `3 ∣ 1350`, so the local factor at `3` of the gap `1350` is `3/2`. -/
