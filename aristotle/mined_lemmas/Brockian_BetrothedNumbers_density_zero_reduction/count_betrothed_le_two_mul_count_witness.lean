/-
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Dependency graph

The goal of this file is to decompose Pollack's theorem (*the set of betrothed,
a.k.a. quasi-amicable, numbers has asymptotic density zero*) into small,
independently reusable pieces, and to prove every piece of the decomposition
that is currently within reach.  The remaining, genuinely analytic, node is
isolated as an explicit hypothesis of the main reduction theorem — it is *not*
assumed anywhere else in the file, and no axiom is added.

```
                      density_zero_reduction            (proved, conditional)
                                 ▲
                                 │
        count_betrothed_le_two_mul_count_witness        (proved)
                ▲                              ▲
                │                              │
   smaller_mem_quasiAmicableWitness     partner_injOn_betrothed   (proved)
                ▲                              ▲
                │                              │
        IsBetrothedPair.symm / partner_eq / sigma1 lemmas         (proved)

   hypothesis node (open, supplied as an argument):
        HasDensityZero quasiAmicableWitness
        i.e.  #{m ≤ x : 2m+1 < σ(m) and σ(σ(m)-m-1) = σ(m)} = o(x)
```

The hypothesis node is *weaker* than Pollack's theorem in the sense that it is a
statement about a set defined by a purely `σ`-arithmetic condition (no
existential quantifier over partners), which is the shape that the
Erdős-type machinery for amicable numbers is usually applied to.  The reduction

lemma count_betrothed_le_two_mul_count_witness (x : ℕ) :
    countUpTo betrothedSet x ≤ 2 * countUpTo quasiAmicableWitness x := by
  classical
  set W : Finset ℕ := (Finset.range (x + 1)).filter (fun n => n ∈ quasiAmicableWitness) with hW
  set B : Finset ℕ := (Finset.range (x + 1)).filter (fun n => n ∈ betrothedSet) with hB
  have hsplit :
      (B.filter (fun n => n ∈ quasiAmicableWitness)).card +
        (B.filter (fun n => ¬ n ∈ quasiAmicableWitness)).card = B.card :=
    Finset.card_filter_add_card_filter_not _
  have h1 : (B.filter (fun n => n ∈ quasiAmicableWitness)).card ≤ W.card := by
    apply Finset.card_le_card
    intro n hn
    simp only [hB, hW, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1.1, hn.2⟩
  have h2 : (B.filter (fun n => ¬ n ∈ quasiAmicableWitness)).card ≤ W.card := by
    refine Finset.card_le_card_of_injOn partner ?_ ?_
    · intro n hn
      simp only [hB, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter,
        Finset.mem_range] at hn
      obtain ⟨⟨hnx, hnb⟩, hnw⟩ := hn
      obtain ⟨m, hpair⟩ := hnb
      have hmn : m < n := by
        rcases lt_trichotomy n m with h | h | h
        · exact absurd (smaller_mem_quasiAmicableWitness hpair h) hnw
        · exact absurd h hpair.2.2.1
        · exact h
      have hp : partner n = m := partner_eq hpair
      simp only [hW, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [hp]
      exact smaller_mem_quasiAmicableWitness hpair.symm hmn
    · intro a ha b hb hab
      simp only [hB, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter,
        Finset.mem_range] at ha hb
      exact partner_injOn_betrothed ha.1.2 hb.1.2 hab
  have : B.card ≤ 2 * W.card := by omega
  simpa [countUpTo, hB, hW, two_mul] using this

/--
**Density zero reduction for betrothed numbers.**

If the (purely `σ`-arithmetically defined) set

`quasiAmicableWitness = {m | 0 < m ∧ 2m + 1 < σ(m) ∧ σ(σ(m) - m - 1) = σ(m)}`

has asymptotic density zero, then the set of betrothed (quasi-amicable) numbers
has asymptotic density zero.

This is the reduction step of Pollack's theorem: it removes the existential
quantifier over partners and the two-sided nature of a betrothed pair, leaving
exactly one analytic node — the density of the witness set — as the remaining
dependency.
-/
