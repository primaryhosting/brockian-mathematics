import Mathlib
/-!
# Van Der Waerden
Category: Frontier Math
Target: Math2.van_der_waerden
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires all `import` commands to precede any other syntax (including module
-- doc comments), so the header block above appears immediately after `import Mathlib`.

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

set_option grind.warning false

namespace Math2

/-- **Van der Waerden's theorem**: for any coloring `C : ℕ → κ` of the naturals by a finite set
of colors `κ`, and any length `k`, there is a monochromatic arithmetic progression
`a, a + d, a + 2d, …, a + (k-1)d` of length `k` with common difference `d > 0`. -/
theorem van_der_waerden {κ : Type*} [Finite κ] (C : ℕ → κ) (k : ℕ) :
    ∃ a d : ℕ, 0 < d ∧ ∃ c : κ, ∀ i < k, C (a + i * d) = c := by
  obtain ⟨a, ha, b, c, hc⟩ := Combinatorics.exists_mono_homothetic_copy (Finset.range k) C
  refine ⟨b, a, ha, c, fun i hi => ?_⟩
  have := hc i (Finset.mem_range.mpr hi)
  rw [smul_eq_mul] at this
  rwa [Nat.mul_comm i a, Nat.add_comm b (a * i)]

/-- Van der Waerden's theorem for an `r`-coloring of `ℕ`, phrased as: all terms of the
progression receive the same color as its first term. -/
theorem van_der_waerden_fin (r k : ℕ) (C : ℕ → Fin r) :
    ∃ a d : ℕ, 0 < d ∧ ∀ i < k, C (a + i * d) = C a := by
  obtain ⟨a, d, hd, c, hc⟩ := van_der_waerden C k
  rcases Nat.eq_zero_or_pos k with hk | hk
  · exact ⟨a, d, hd, fun i hi => absurd hi (by omega)⟩
  · refine ⟨a, d, hd, fun i hi => ?_⟩
    have h0 : C a = c := by simpa using hc 0 hk
    rw [hc i hi, h0]

end Math2

