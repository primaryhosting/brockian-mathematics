/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix ComplexConjugate
open scoped BigOperators ComplexOrder

namespace QI

/-! ## Linear-algebra preliminaries -/

section RankLemmas

variable {X Y : Type*}

/-- Rank–nullity for the linear map `v ↦ M *ᵥ v`. -/

lemma glue_splitA (S1 S2 : Finset (Fin n)) (hdisj : ∀ i, i ∈ S1 → i ∉ S2)
    (a : {i : Fin n // i ∈ S1} → Fin q) (b : {i : Fin n // i ∉ S1 ∧ i ∉ S2} → Fin q)
    (c : {i : Fin n // i ∈ S2} → Fin q) :
    glue S2 c (splitA S1 S2 hdisj (a, b)) = merge3 S1 S2 a b c := by
  funext t
  by_cases h1 : t ∈ S1 <;> by_cases h2 : t ∈ S2 <;> simp [glue, merge3, splitA, h1, h2]
  · exact absurd h2 (hdisj t h1)

/-! ## The quantum Singleton bound -/

/-- **Quantum Singleton bound.**  Let `V` be an isometric encoding of a `K = q ^ k`-dimensional
code into `n` qudits of local dimension `q ≥ 2`, and suppose the code has distance `d ≥ 1`,
i.e. the erasure of any set of at most `d - 1` qudits is correctable (Knill–Laflamme condition).
Then `n - k ≥ 2 (d - 1)`, stated in the subtraction-free form `2 * (d - 1) + k ≤ n`.

The hypothesis `1 ≤ k` is genuinely needed: a one-dimensional "code" (`k = 0`) trivially
satisfies the erasure conditions for every set of qudits. -/
