/-
# Van Der Waerden
Category: Frontier Math
Target: Math2.van_der_waerden
Statement: Any finite coloring of ℕ has arbitrarily long monochromatic APs (van der Waerden).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math2

/-- `HasAP c m N` says the coloring `c` admits a monochromatic arithmetic progression of
length `m` with positive common difference, contained (together with a little slack) in
`[0, N]`. -/

theorem vdw_step {k : ℕ} (hk : 1 ≤ k) (Wk : VDW k) : VDW (k + 1) := by
  intro K _
  obtain ⟨N, hN⟩ := fan_induction (K := K) hk Wk (Nat.card K + 1)
  refine ⟨N, fun c => ?_⟩
  rcases hN c with h | ⟨f, a, d, _, _, _, _, hinj⟩
  · exact h
  · exfalso
    have hginj : Function.Injective (fun j : Fin (Nat.card K + 1) => c (a j)) := by
      intro i j hij
      have := hinj i i.isLt j j.isLt hij
      exact Fin.ext this
    have := Nat.card_le_card_of_injective _ hginj
    simp at this

