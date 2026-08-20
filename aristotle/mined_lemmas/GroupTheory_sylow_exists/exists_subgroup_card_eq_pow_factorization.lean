/-
# Sylow Exists
Category: Frontier Wave 2 (deeper machinery)
Target: GroupTheory.sylow_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace GroupTheory

open scoped Pointwise

/-- Key intermediate lemma: for a finite group `G` and a prime `p`, there is a subgroup of `G`
whose cardinality is `p ^ n`, where `p ^ n` is the largest power of `p` dividing `|G|`.
This is the substantive content of Sylow's first theorem. -/

theorem exists_subgroup_card_eq_pow_factorization
    (G : Type*) [Group G] [Fintype G] (p : ℕ) (hp : p.Prime) :
    ∃ H : Subgroup G, Nat.card H = p ^ (Nat.card G).factorization p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨H, hH⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := G) p
      (n := (Nat.card G).factorization p) (Nat.ordProj_dvd _ p)
  exact ⟨H, by simpa using hH⟩

/-- A subgroup whose cardinality is the maximal `p`-power dividing `|G|` is a Sylow
`p`-subgroup, hence `Sylow p G` is nonempty. -/
