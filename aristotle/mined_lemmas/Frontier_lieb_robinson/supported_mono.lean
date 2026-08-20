/-
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is a plain block comment because Lean 4 requires `import` commands to
-- precede every other command, including module doc-strings.)

import Mathlib

/-!
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
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

namespace Frontier

/-- Spin configurations of a chain of `N` sites (each site carries a qubit). -/
abbrev Config (N : ℕ) := Fin N → Fin 2

/-- Observables of the spin chain: linear operators on the `2^N`-dimensional Hilbert space,
represented as matrices indexed by spin configurations. -/
abbrev SpinOp (N : ℕ) := Matrix (Config N) (Config N) ℂ

/-- `Supported S M` says that the observable `M` acts only on the sites in `S`, i.e.
`M = M₀ ⊗ 1` with `M₀` acting on the sites of `S`.  Concretely, matrix elements vanish
unless the configurations agree off `S`, and they depend only on the restrictions to `S`. -/

theorem supported_mono {S T : Set (Fin N)} {M : SpinOp N} (hST : S ⊆ T)
    (hM : Supported S M) : Supported T M := by
  obtain ⟨h0, h1⟩ := hM
  refine ⟨fun c d hne => ?_, fun c d c' d' hcc' hdd' hcd hc'd' => ?_⟩
  · obtain ⟨i, hi, hne⟩ := hne
    exact h0 c d ⟨i, fun hiS => hi (hST hiS), hne⟩
  · by_cases hdiag : ∀ i, i ∉ S → c i = d i
    · refine h1 c d c' d' (fun i hi => hcc' i (hST hi)) (fun i hi => hdd' i (hST hi)) hdiag ?_
      intro i hi
      by_cases hiT : i ∈ T
      · rw [← hcc' i hiT, ← hdd' i hiT]; exact hdiag i hi
      · exact hc'd' i hiT
    · push_neg at hdiag
      obtain ⟨i, hiS, hne⟩ := hdiag
      have hiT : i ∈ T := by
        by_contra hiT
        exact hne (hcd i hiT)
      rw [h0 c d ⟨i, hiS, hne⟩,
        h0 c' d' ⟨i, hiS, by rw [← hcc' i hiT, ← hdd' i hiT]; exact hne⟩]

