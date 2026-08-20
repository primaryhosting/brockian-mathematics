/-!
# Bolzano Weierstrass
Category: Frontier Wave 2 (deeper machinery)
Target: Topology.bolzano_weierstrass
Statement: Bolzano-Weierstrass: a sequence taking values in a compact set has a convergent subsequence. State: for a compact set s in a metric space and a sequence f : Nat -> s-underlying with all f n ∈ s, there is a subsequence converging to a point of s. (Use Mathlib's IsCompact.tendsto_subseq.)
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Bolzano Weierstrass
Category: Frontier Wave 2 (deeper machinery)
Target: Topology.bolzano_weierstrass
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
# Bolzano Weierstrass
Category: Frontier Wave 2 (deeper machinery)
Target: Topology.bolzano_weierstrass
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Topology

/-- **Bolzano–Weierstrass**: a sequence taking values in a compact subset `s` of a
metric space has a subsequence converging to a point of `s`.  Concretely, there is
a strictly monotone index map `φ : ℕ → ℕ` and a point `a ∈ s` such that
`f ∘ φ` tends to `a`. -/
theorem bolzano_weierstrass {X : Type*} [MetricSpace X] {s : Set X} (hs : IsCompact s)
    (f : ℕ → X) (hf : ∀ n, f n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Filter.Tendsto (f ∘ φ) Filter.atTop (nhds a) :=
  hs.tendsto_subseq hf

end Topology

