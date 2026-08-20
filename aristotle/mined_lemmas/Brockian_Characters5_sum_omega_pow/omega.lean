import Mathlib

/-!
# Sum Omega Pow
Category: Characters
Target: Brockian.Characters5.sum_omega_pow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian
namespace Characters5

/-- A primitive 5th root of unity. -/

noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

@[inherit_doc] scoped notation "ω" => Brockian.Characters5.omega

/-- `ω` is a primitive 5th root of unity. -/
