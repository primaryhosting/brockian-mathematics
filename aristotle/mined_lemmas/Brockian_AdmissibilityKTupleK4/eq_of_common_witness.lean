/-!
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean requires every `import` line to precede all other commands, while the
required header above is itself a command (a module docstring).  The development below is
therefore written against the Lean 4 core library only, with no `import` line, so that the
file both begins with the exact required header and compiles.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- Primality, spelled out without Mathlib: `p ≥ 2` and the only divisors of `p` are `1` and
`p`. -/

theorem eq_of_common_witness {p x a b : Int} (hp : 5 ≤ p) (h1 : p ∣ (x - a)) (h2 : p ∣ (x - b))
    (ha0 : 0 ≤ a) (ha : a < 5) (hb0 : 0 ≤ b) (hb : b < 5) : a = b := by
  obtain ⟨c, hc⟩ := h1
  obtain ⟨d, hd⟩ := h2
  refine eq_of_dvd_sub_of_small hp ⟨d - c, ?_⟩ ha0 ha hb0 hb
  have : a - b = p * d - p * c := by omega
  rw [this, Int.mul_sub]

/-! ## The four entries of a `4`-tuple, indexed by `Nat` -/

/-- The `i`-th entry of the `4`-tuple `(h₀, h₁, h₂, h₃)`. -/
