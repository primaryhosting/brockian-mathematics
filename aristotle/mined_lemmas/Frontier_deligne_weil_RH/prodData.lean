/-
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
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

/-- The cohomological data attached to a smooth projective variety of dimension `dim`
over the finite field `𝔽_q`: for each degree `i`, the multiset `eigen i` of eigenvalues
of the geometric Frobenius acting on the `i`-th ℓ-adic cohomology group. -/
structure WeilData where
  /-- The cardinality of the base finite field. -/
  q : ℕ
  /-- The base field is a genuine finite field. -/
  hq : 1 < q
  /-- The dimension of the variety. -/
  dim : ℕ
  /-- Multiset of Frobenius eigenvalues in cohomological degree `i`. -/
  eigen : ℕ → Multiset ℂ
  /-- Cohomology vanishes above degree `2 * dim`. -/
  vanish : ∀ i, 2 * dim < i → eigen i = 0
  /-- Frobenius acts invertibly, so all eigenvalues are nonzero. -/
  nonzero : ∀ i, ∀ a ∈ eigen i, a ≠ 0

namespace WeilData

variable (W : WeilData)

/-- The Lefschetz trace formula prediction for the number of `𝔽_{q^m}`-rational points:
`N_m = ∑_i (-1)^i tr(Frob^m ∣ H^i)`. -/

noncomputable def prodData (W₁ W₂ : WeilData) (hq : W₁.q = W₂.q) : WeilData where
  q := W₁.q
  hq := by rw [hq]; exact W₂.hq
  dim := W₁.dim + W₂.dim
  eigen := fun k =>
    ∑ i ∈ Finset.range (k + 1),
      (W₁.eigen i).bind (fun a => (W₂.eigen (k - i)).map (fun b => a * b))
  vanish := by
    intro k hk
    refine Finset.sum_eq_zero ?_
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro x hx
    rw [Multiset.mem_bind] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    by_cases h : 2 * W₁.dim < i
    · rw [W₁.vanish i h] at ha
      exact absurd ha (Multiset.notMem_zero a)
    · have h2 : 2 * W₂.dim < k - i := by omega
      rw [W₂.vanish _ h2] at hxa
      simp at hxa
  nonzero := by
    intro k a ha
    rw [Multiset.mem_sum] at ha
    obtain ⟨i, _, hai⟩ := ha
    rw [Multiset.mem_bind] at hai
    obtain ⟨x, hx, hax⟩ := hai
    rw [Multiset.mem_map] at hax
    obtain ⟨y, hy, rfl⟩ := hax
    exact mul_ne_zero (W₁.nonzero i x hx) (W₂.nonzero (k - i) y hy)

/-- **Künneth stability.** If the Riemann hypothesis holds for two varieties over `𝔽_q`,
it holds for their product. -/
