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

theorem RH_prodData (W₁ W₂ : WeilData) (hq : W₁.q = W₂.q) (h₁ : W₁.RH) (h₂ : W₂.RH) :
    (prodData W₁ W₂ hq).RH := by
  have hq0 : (0 : ℝ) < (W₁.q : ℝ) := by
    have h1 := W₁.hq; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1.le
  intro k a ha
  have heig : (prodData W₁ W₂ hq).eigen k
      = ∑ i ∈ Finset.range (k + 1),
        (W₁.eigen i).bind (fun a => (W₂.eigen (k - i)).map (fun b => a * b)) := rfl
  have hqq : (prodData W₁ W₂ hq).q = W₁.q := rfl
  rw [heig, Multiset.mem_sum] at ha
  obtain ⟨i, hi, hai⟩ := ha
  simp only [Finset.mem_range] at hi
  rw [Multiset.mem_bind] at hai
  obtain ⟨x, hx, hax⟩ := hai
  rw [Multiset.mem_map] at hax
  obtain ⟨y, hy, rfl⟩ := hax
  rw [hqq, norm_mul, h₁ i x hx, h₂ (k - i) y hy, ← hq, ← Real.rpow_add hq0]
  congr 1
  have hik : (i : ℝ) + ((k - i : ℕ) : ℝ) = (k : ℝ) := by
    have hik' : i ≤ k := by omega
    push_cast [Nat.cast_sub hik']
    ring
  field_simp
  linarith [hik]

/-! ### The Hasse–Weil bound for curves -/

/-- **The Hasse–Weil bound.** For a curve of genus `g` over `𝔽_q` (so `H^0` and `H^2` are
spanned by `1` and `q` and `H^1` has dimension `2g`), the Riemann hypothesis is exactly
what gives the classical estimate `|N_m - (q^m + 1)| ≤ 2g·q^{m/2}` on the number of
`𝔽_{q^m}`-rational points. -/
