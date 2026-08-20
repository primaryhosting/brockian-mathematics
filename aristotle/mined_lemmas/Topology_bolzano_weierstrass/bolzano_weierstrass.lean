/-
# Bolzano Weierstrass
Category: Frontier Wave 2 (deeper machinery)
Target: Topology.bolzano_weierstrass
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bolzano Weierstrass
Category: Frontier Wave 2 (deeper machinery)
Target: Topology.bolzano_weierstrass
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Topology

/-- **Bolzano–Weierstrass theorem.**  In a metric space, any sequence `f : ℕ → X` whose values
all lie in a compact set `s` admits a strictly monotone reindexing `g : ℕ → ℕ` such that the
subsequence `f ∘ g` converges to some point `a ∈ s`.

This is a direct instance of Mathlib's `IsCompact.tendsto_subseq` (a metric space is a
first-countable topological space). -/

theorem bolzano_weierstrass {X : Type*} [MetricSpace X] {s : Set X} (hs : IsCompact s)
    (f : ℕ → X) (hf : ∀ n : ℕ, f n ∈ s) :
    ∃ a ∈ s, ∃ g : ℕ → ℕ, StrictMono g ∧ Filter.Tendsto (f ∘ g) Filter.atTop (nhds a) :=
  hs.tendsto_subseq hf

end Topology

