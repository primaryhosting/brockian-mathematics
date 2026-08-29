/-
# Hales Jewett
Category: Frontier Math
Target: Math2.hales_jewett
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Hales Jewett
Category: Frontier Math
Target: Math2.hales_jewett
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

namespace Math2

/-- A *combinatorial line* in the cube `(Fin N → Fin a)` is described by a template
`τ : Fin N → Option (Fin a)`: coordinates with `τ i = some v` are frozen to the value `v`,
while coordinates with `τ i = none` all carry the moving variable `x`.
`linePoint τ x` is the point of the line corresponding to the value `x` of the variable. -/
def linePoint {N a : ℕ} (τ : Fin N → Option (Fin a)) (x : Fin a) : Fin N → Fin a :=
  fun i => (τ i).getD x

/-- **The Hales–Jewett theorem.** For any alphabet size `a` and any number of colours `k`
there is a dimension `N` such that every `k`-colouring of the cube `(Fin N → Fin a)`
admits a monochromatic combinatorial line: a template `τ` with at least one moving
coordinate whose points `linePoint τ x`, `x : Fin a`, all receive the same colour. -/
theorem hales_jewett (a k : ℕ) :
    ∃ N : ℕ, ∀ C : (Fin N → Fin a) → Fin k,
      ∃ τ : Fin N → Option (Fin a), (∃ i, τ i = none) ∧
        ∃ c : Fin k, ∀ x : Fin a, C (linePoint τ x) = c := by
  obtain ⟨ι, ιfin, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin a) (Fin k)
  refine ⟨Fintype.card ι, fun C => ?_⟩
  set e := Fintype.equivFin ι
  obtain ⟨l, c, hc⟩ := hι (fun v => C (v ∘ e.symm))
  refine ⟨fun j => l.idxFun (e.symm j), ?_, c, fun x => ?_⟩
  · obtain ⟨i, hi⟩ := l.proper
    exact ⟨e i, by simpa using hi⟩
  · rw [← hc x]
    rfl

end Math2

