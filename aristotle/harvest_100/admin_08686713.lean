/-
# Bolzano Weierstrass
Category: Pure Mathematics
Target: Math.bolzano_weierstrass
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bolzano Weierstrass
Category: Pure Mathematics
Target: Math.bolzano_weierstrass
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open Filter Metric

/-- **Bolzano–Weierstrass theorem in `ℝ^n`.**
Every bounded sequence `x : ℕ → EuclideanSpace ℝ (Fin n)` (i.e. `‖x k‖ ≤ C` for all `k`)
admits a strictly monotone index map `φ : ℕ → ℕ` such that the subsequence `x ∘ φ`
converges to some point `a` of `ℝ^n`, which moreover satisfies `‖a‖ ≤ C`. -/
theorem bolzano_weierstrass {n : ℕ} (x : ℕ → EuclideanSpace ℝ (Fin n)) {C : ℝ}
    (hC : ∀ k, ‖x k‖ ≤ C) :
    ∃ a : EuclideanSpace ℝ (Fin n), ‖a‖ ≤ C ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (nhds a) := by
  -- The closed ball of radius `C` centred at the origin is compact (Heine–Borel),
  -- and the sequence lives in it.
  have hcompact : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) C) :=
    isCompact_closedBall _ _
  have hmem : ∀ k, x k ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) C := by
    intro k
    simpa [Metric.mem_closedBall, dist_eq_norm] using hC k
  obtain ⟨a, ha, φ, hφ, hlim⟩ := hcompact.tendsto_subseq hmem
  refine ⟨a, ?_, φ, hφ, hlim⟩
  simpa [Metric.mem_closedBall, dist_eq_norm] using ha

/-- Set-theoretic phrasing: a sequence in `ℝ^n` whose range is a bounded set has a
convergent subsequence. -/
theorem bolzano_weierstrass_of_isBounded {n : ℕ} (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hb : Bornology.IsBounded (Set.range x)) :
    ∃ a : EuclideanSpace ℝ (Fin n), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (x ∘ φ) atTop (nhds a) := by
  obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le).1 hb
  obtain ⟨a, _, φ, hφ, hlim⟩ :=
    bolzano_weierstrass x (C := C) fun k => hC (x k) ⟨k, rfl⟩
  exact ⟨a, φ, hφ, hlim⟩

end Math

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

