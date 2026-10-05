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

theorem RH_of_le_dim_of_poincareDuality (W : WeilData) (hPD : W.PoincareDuality)
    (h : ∀ i ≤ W.dim, ∀ a ∈ W.eigen i, ‖a‖ = (W.q : ℝ) ^ ((i : ℝ) / 2)) : W.RH := by
  have hq0 : (0 : ℝ) < (W.q : ℝ) := by
    have h1 := W.hq; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1.le
  intro i a ha
  by_cases hle : i ≤ W.dim
  · exact h i hle a ha
  by_cases hbig : 2 * W.dim < i
  · rw [W.vanish i hbig] at ha
    exact absurd ha (Multiset.notMem_zero a)
  · push_neg at hle
    set j := 2 * W.dim - i with hj
    have hji : 2 * W.dim - j = i := by omega
    have hjd : j ≤ W.dim := by omega
    have hj2 : j ≤ 2 * W.dim := by omega
    have hdual := hPD j hj2
    rw [hji] at hdual
    rw [hdual, Multiset.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    have hbn := h j hjd b hb
    rw [norm_div, hbn, norm_pow, Complex.norm_natCast,
      ← Real.rpow_natCast (W.q : ℝ) W.dim, ← Real.rpow_sub hq0]
    congr 1
    have hcast : (i : ℝ) + (j : ℝ) = 2 * (W.dim : ℝ) := by
      have hij : i + j = 2 * W.dim := by omega
      exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) hij
    linarith

/-! ### Künneth: the Riemann hypothesis is stable under products -/

/-- The Weil data of a product of two varieties over the same finite field: by the Künneth
formula the degree-`k` eigenvalues are the products `a·b` with `a` in degree `i` and `b` in
degree `k - i`. -/
