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

theorem paley_compl_no_clique (s : Finset (Fin 17)) : ¬ paleyᶜ.IsNClique 4 s := by
  intro h
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := card_eq_four h.2
  have hcl := h.1
  simp only [Finset.coe_insert, Finset.coe_singleton] at hcl
  have hstep : ∀ x y : Fin 17, paleyᶜ.Adj x y → qr17 (x - y) = false := by
    intro x y hxy
    have := (SimpleGraph.compl_adj _ x y).mp hxy
    simpa [paley] using this.2
  refine (paley_check a b c d hab hac had hbc hbd hcd).2 ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hstep _ _ (hcl (by simp) (by simp) hab)
  · exact hstep _ _ (hcl (by simp) (by simp) hac)
  · exact hstep _ _ (hcl (by simp) (by simp) had)
  · exact hstep _ _ (hcl (by simp) (by simp) hbc)
  · exact hstep _ _ (hcl (by simp) (by simp) hbd)
  · exact hstep _ _ (hcl (by simp) (by simp) hcd)

/-- Pulling a clique back along an injection. -/
