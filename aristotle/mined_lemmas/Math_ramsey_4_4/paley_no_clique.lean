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

theorem paley_no_clique (s : Finset (Fin 17)) : ¬ paley.IsNClique 4 s := by
  intro h
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := card_eq_four h.2
  have hcl := h.1
  simp only [Finset.coe_insert, Finset.coe_singleton] at hcl
  refine (paley_check a b c d hab hac had hbc hbd hcd).1 ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hcl (by simp) (by simp) hab
  · exact hcl (by simp) (by simp) hac
  · exact hcl (by simp) (by simp) had
  · exact hcl (by simp) (by simp) hbc
  · exact hcl (by simp) (by simp) hbd
  · exact hcl (by simp) (by simp) hcd

