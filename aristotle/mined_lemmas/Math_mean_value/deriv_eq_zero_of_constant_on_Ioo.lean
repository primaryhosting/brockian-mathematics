/-
# Mean Value
Category: Pure Mathematics
Target: Math.mean_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Set

namespace Math

/-- If `f` is constant on an open interval, its derivative vanishes at interior points. -/

theorem deriv_eq_zero_of_constant_on_Ioo {f : ℝ → ℝ} {a b c : ℝ} (hc : c ∈ Ioo a b)
    (hconst : ∀ x ∈ Ioo a b, f x = f c) : deriv f c = 0 := by
  have h : f =ᶠ[nhds c] fun _ => f c := by
    filter_upwards [isOpen_Ioo.mem_nhds hc] with x hx using hconst x hx
  rw [h.deriv_eq, deriv_const]

/-- **Rolle's theorem**: a function continuous on `[a,b]` taking equal values at the endpoints
has a critical point in `(a,b)`.

(Differentiability is not needed as a hypothesis: at a point where `f` is not differentiable,
Mathlib's junk value convention already gives `deriv f = 0`.) -/
