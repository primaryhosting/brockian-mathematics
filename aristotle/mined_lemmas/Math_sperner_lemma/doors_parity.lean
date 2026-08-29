/-
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open Finset

variable {V : Type*} [DecidableEq V]

/-- The number of cells of `K` that contain the face `τ`. -/

theorem doors_parity (c : V → ℕ) (n : ℕ) (σ : Finset V) (hcard : σ.card = n + 2)
    (hsub : σ.image c ⊆ range (n + 2)) :
    (doorsOf c n σ).card % 2 = if σ.image c = range (n + 2) then 1 else 0 := by
  by_cases hcov : range (n + 1) ⊆ σ.image c
  · by_cases hn : (n + 1) ∈ σ.image c
    · have himg : σ.image c = range (n + 2) := by
        refine Finset.Subset.antisymm hsub ?_
        intro k hk
        rw [Finset.mem_range] at hk
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
        · exact hcov (Finset.mem_range.2 h)
        · rw [h]; exact hn
      rw [doors_of_rainbow c n σ hcard himg, if_pos himg]
    · have himg : σ.image c = range (n + 1) := by
        refine Finset.Subset.antisymm ?_ hcov
        intro k hk
        have hk' : k ∈ range (n + 2) := hsub hk
        rw [Finset.mem_range] at hk' ⊢
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with h | h
        · exact h
        · exact absurd (h ▸ hk) hn
      have hne : σ.image c ≠ range (n + 2) := by
        rw [himg]
        intro hcon
        apply hn
        rw [himg, hcon]
        simp
      rw [doors_of_almost c n σ hcard himg, if_neg hne]
  · have hne : σ.image c ≠ range (n + 2) := by
      intro hcon
      apply hcov
      rw [hcon]
      intro k hk
      rw [Finset.mem_range] at hk ⊢
      omega
    rw [doors_of_other c n σ hcov, if_neg hne]

/-! ### The main theorem -/

/-- **Sperner's lemma.** For any triangulation `K` of the `n`-simplex and any Sperner colouring
`c` (each vertex `v` receives a colour `c v` belonging to its carrier face `s v`), the number of
rainbow cells — cells whose vertices carry all `n + 1` colours — is odd. -/
