import Mathlib
/-!
# Bolzano Weierstrass
Category: Frontier Wave 2 (deeper machinery)
Target: Topology.bolzano_weierstrass
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Topology

/-- **Bolzano–Weierstrass**: a sequence taking values in a compact set `s` of a
metric space has a subsequence converging to a point of `s`. -/
theorem bolzano_weierstrass {X : Type*} [MetricSpace X] {s : Set X}
    (hs : IsCompact s) (f : ℕ → X) (hf : ∀ n, f n ∈ s) :
    ∃ a ∈ s, ∃ g : ℕ → ℕ, StrictMono g ∧ Filter.Tendsto (f ∘ g) Filter.atTop (nhds a) :=
  hs.tendsto_subseq hf

end Topology

