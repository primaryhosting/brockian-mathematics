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

lemma countUpTo_le_card_of_finite {S : Set ℕ} (hS : S.Finite) (x : ℕ) :
    countUpTo S x ≤ hS.toFinset.card := by
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn
  simpa using hn.2

/-- Comparison criterion: if the counting function of `S` is bounded by a
constant multiple of the counting function of a density-zero set, then `S` has
density zero. -/
