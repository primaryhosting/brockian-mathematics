import Mathlib

/-!
# Brockian packaging of the Hawking focusing / singularity argument

This file contains

* `Brockian.Frontier.raychaudhuri_focusing_general`: the analytic core.  If a real function
  `theta` ("expansion") satisfies a Raychaudhuri-type differential inequality
  `theta' ≤ -theta ^ 2 / n` on `[0, L)` and starts negative, then `L ≤ -n / theta 0`.
  The constant `n` is the number of transverse dimensions: `n = 3` for a timelike
  congruence in `3 + 1` dimensions (Hawking), `n = 2` for a null congruence (Penrose).

* `Brockian.Frontier.TimelikeCongruence` and `Brockian.Frontier.hawking_focusing`: the
  timelike (`n = 3`) packaging requested, and its proof.

* `Brockian.Frontier.NullCongruence` and `Brockian.Frontier.penrose_focusing`: the null
  (`n = 2`) specialisation, for comparison.

* `Brockian.Frontier.ExpandingCauchy`, `Brockian.Frontier.TimelikeGeodesicallyComplete`
  and `Brockian.Frontier.hawking_singularity`: a geometric packaging of the cosmological
  setting.  Since Mathlib has no Lorentzian geometry, the packaging is *abstract*: the
  data of a Cauchy surface with a uniformly expanding orthogonal geodesic congruence is
  recorded as the family of expansion scalars along the generators together with the
  Raychaudhuri inequality (which encodes the strong energy condition and vanishing
  vorticity) and the uniform expansion bound `theta i 0 ≤ -c < 0`.  Timelike geodesic
  completeness is taken in the form it is actually used in Hawking's argument: every
  generator can be continued, with a smooth expansion scalar, to arbitrarily large proper
  time.  The theorem says this is impossible.
-/

namespace Brockian.Frontier

open Set

/-! ### The analytic focusing lemma -/

/-- **Raychaudhuri focusing, general transverse dimension.**

If `theta : ℝ → ℝ` has derivative `dtheta` on `[0, L)`, satisfies the Raychaudhuri
inequality `dtheta τ ≤ -(theta τ) ^ 2 / n` there (`n > 0`), and is negative at `τ = 0`,
then the interval on which this is possible has length at most `-n / theta 0`.

Proof: `theta` is antitone, hence stays `≤ theta 0 < 0`; therefore `1 / theta` is
differentiable with derivative `-dtheta / theta ^ 2 ≥ 1 / n`, so
`1 / theta τ ≥ 1 / theta 0 + τ / n`, while `1 / theta τ < 0`. -/

theorem hawking_singularity {ι : Type*} (C : ExpandingCauchy ι) :
    ¬ TimelikeGeodesicallyComplete C := by
  intro hcomplete
  obtain ⟨i⟩ := C.hne
  set L : ℝ := 3 / C.c + 1 with hL
  have h0 : C.theta i 0 < 0 := lt_of_le_of_lt (C.hexpand i) (by linarith [C.hc])
  have hbound : L ≤ -3 / C.theta i 0 :=
    raychaudhuri_focusing_general (n := 3) (by norm_num)
      (fun τ hτ => hcomplete i τ hτ.1) (fun τ hτ => C.hRay i τ hτ.1) h0
  -- but `-3 / theta i 0 ≤ 3 / c < L`
  have hθ : C.c ≤ -C.theta i 0 := by linarith [C.hexpand i]
  have heq : -3 / C.theta i 0 = 3 / (-C.theta i 0) := by rw [div_neg, ← neg_div]
  have hle : -3 / C.theta i 0 ≤ 3 / C.c := by
    rw [heq]
    exact div_le_div_of_nonneg_left (by norm_num) C.hc hθ
  rw [hL] at hbound
  linarith

/-- Sanity check: the hypotheses of `ExpandingCauchy` are satisfiable, so
`hawking_singularity` is not vacuous.  (In this toy datum the expansion is the constant
`-1`; it is completeness, i.e. the requirement that `dtheta` really is the derivative of
`theta` for all future proper times, that fails.) -/
example : ExpandingCauchy Unit :=
  { hne := ⟨()⟩
    theta := fun _ _ => -1
    dtheta := fun _ _ => -1
    c := 1
    hc := one_pos
    hRay := by intro i τ _; norm_num
    hexpand := by intro i; norm_num }

end Brockian.Frontier

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

