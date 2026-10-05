import Mathlib

/-!
# Hales Jewett
Category: Frontier Math
Target: Math2.hales_jewett
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to be the very first commands in a file, so the
-- header module docstring above is placed immediately after the single `import Mathlib` line.

namespace Math2

/-- **The Hales–Jewett theorem** (finitary form, stated elementarily).

For every alphabet size `k` and every number of colours `r` there is a dimension `N` such that
every `r`-colouring `C` of the combinatorial cube `Fin N → Fin k` contains a monochromatic
combinatorial line.

A combinatorial line is described by a *template* `τ : Fin N → Option (Fin k)`: coordinates with
`τ i = some a` are frozen to the letter `a`, while coordinates with `τ i = none` are *wildcards*.
Nondegeneracy of the line is the requirement that at least one wildcard occurs. The point of the
line corresponding to the letter `x : Fin k` is `fun i => (τ i).getD x`, i.e. every wildcard is
filled in with `x`. Monochromaticity says that all `k` points of the line get the same colour. -/
theorem hales_jewett (k r : ℕ) :
    ∃ N : ℕ, ∀ C : (Fin N → Fin k) → Fin r,
      ∃ τ : Fin N → Option (Fin k),
        (∃ i, τ i = none) ∧
        ∀ x y : Fin k, C (fun i => (τ i).getD x) = C (fun i => (τ i).getD y) := by
  obtain ⟨ι, _, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin k) (Fin r)
  obtain ⟨e⟩ : Nonempty (ι ≃ Fin (Fintype.card ι)) := ⟨Fintype.equivFin ι⟩
  refine ⟨Fintype.card ι, fun C => ?_⟩
  obtain ⟨l, c, hc⟩ := hι fun v => C fun i => v (e.symm i)
  refine ⟨fun i => l.idxFun (e.symm i), ?_, fun x y => ?_⟩
  · obtain ⟨i, hi⟩ := l.proper
    exact ⟨e i, by simpa using hi⟩
  · have h : ∀ z : Fin k, C (fun i => (l.idxFun (e.symm i)).getD z) = c := by
      intro z; simpa using hc z
    rw [h x, h y]

end Math2

import Mathlib

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

