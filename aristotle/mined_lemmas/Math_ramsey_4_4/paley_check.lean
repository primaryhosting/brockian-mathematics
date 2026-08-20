/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Math

open Finset

/-- `RamseyProp N p q` says: for every red/blue colouring of the edges of a complete graph
(the red edges being the edges of a simple graph `G`), every set `t` of at least `N` vertices
contains a red clique of size `p` or a blue clique of size `q`.
Here "blue" means an edge of the complement `Gᶜ`. -/

theorem paley_check : ∀ a b c d : Fin 17, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ¬(qr17 (a - b) ∧ qr17 (a - c) ∧ qr17 (a - d) ∧ qr17 (b - c) ∧ qr17 (b - d) ∧ qr17 (c - d)) ∧
    ¬(qr17 (a - b) = false ∧ qr17 (a - c) = false ∧ qr17 (a - d) = false ∧
        qr17 (b - c) = false ∧ qr17 (b - d) = false ∧ qr17 (c - d) = false) := by
  decide

/-- Any `4`-element set is of the form `{a, b, c, d}` with the four elements distinct. -/
