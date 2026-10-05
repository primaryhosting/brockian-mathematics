/-
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- The `r`-neighbourhood of a set of sites `X` inside a metric space of sites. -/

theorem norm_evol_le (u v : ℕ → A)
    (hnu : ∀ k, ‖u k‖ ≤ 1) (hnv : ∀ k, ‖v k‖ ≤ 1) (a : A) (n : ℕ) :
    ‖evol u v n a‖ ≤ ‖a‖ := by
  induction n with
  | zero => simp [evol]
  | succ k ih =>
      have h1 : ‖evol u v (k + 1) a‖ ≤ ‖u k * evol u v k a‖ * ‖v k‖ := by
        show ‖u k * evol u v k a * v k‖ ≤ _
        exact norm_mul_le _ _
      have h2 : ‖u k * evol u v k a‖ ≤ ‖u k‖ * ‖evol u v k a‖ := norm_mul_le _ _
      have h3 : (0 : ℝ) ≤ ‖evol u v k a‖ := norm_nonneg _
      have h4 : (0 : ℝ) ≤ ‖v k‖ := norm_nonneg _
      have h6 : ‖u k‖ * ‖evol u v k a‖ ≤ ‖a‖ := by
        nlinarith [hnu k, norm_nonneg (u k)]
      have h7 : (‖u k‖ * ‖evol u v k a‖) * ‖v k‖ ≤ ‖a‖ * 1 :=
        mul_le_mul h6 (hnv k) h4 (norm_nonneg a)
      have h5 : ‖u k * evol u v k a‖ * ‖v k‖ ≤ (‖u k‖ * ‖evol u v k a‖) * ‖v k‖ :=
        mul_le_mul_of_nonneg_right h2 h4
      linarith

end

/-- **Lieb–Robinson bound (discrete-time / finite-range special case).**

Let `A` be a normed ring of observables equipped with a locality structure `loc`, assigning to
each region `S` of a metric space of sites a set of observables `loc S`, monotone in `S`, closed
under products, and such that observables attached to disjoint regions commute.

Consider a discrete-time dynamics given by `n` layers of local gates: at step `k` one conjugates
by a contraction `u k` with inverse `v k`, both supported in a region `Z k` of diameter at most
`1` (i.e. the interaction has range one, so the Lieb–Robinson velocity is `1` site per layer).

Then for observables `a` supported in `X` and `b` supported in `Y` whose regions are at distance
at least `r`, the commutator of the evolved observable with `b` obeys the light-cone bound
`‖[τₙ(a), b]‖ ≤ 2‖a‖‖b‖ exp (n - r)`.

Indeed the commutator vanishes identically outside the light cone `r ≤ n`, and inside it the
exponential factor is at least `1`. -/
