/-
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` to come first in a file, so the header above the import is a plain
block comment and this is the module docstring with the same content.)

Mathlib does not contain Ramsey numbers, so the whole development is built here:
the recursion `R(3,t+1) ≤ t + R(3,t)`, the parity refinement giving `R(3,4) ≤ 9`,
hence `R(3,5) ≤ 14`, and the circulant graph `C₁₃(1,5)` witnessing `R(3,5) > 13`.
-/

set_option maxHeartbeats 2000000

namespace Math

open Finset

/-! ## The Ramsey property -/

/-- `RamseyProp n s t` says that every simple graph on `n` vertices contains either a clique
of size `s` or an independent set of size `t` (equivalently, a clique of size `t` in the
complement).  `R(s,t)` is the least `n` with this property. -/

theorem not_ramseyProp_of_le_thirteen {n : ℕ} (hn : n ≤ 13) : ¬ RamseyProp n 3 5 := by
  intro h
  set f : Fin n ↪ Fin 13 := ⟨Fin.castLE hn, Fin.castLE_injective hn⟩ with hf
  have hcompl : (SimpleGraph.comap (⇑f) G13)ᶜ = SimpleGraph.comap (⇑f) G13ᶜ := by
    ext a b
    simp [hf, SimpleGraph.comap, Fin.castLE_inj]
  rcases h (SimpleGraph.comap (⇑f) G13) with h3 | h5
  · exact h3 (G13_cliqueFree_three.comap (SimpleGraph.Embedding.comap f G13))
  · rw [hcompl] at h5
    exact h5 (G13_compl_cliqueFree_five.comap (SimpleGraph.Embedding.comap f G13ᶜ))

/-! ## The Ramsey number -/

/-- `R(3,5) = 14`: `14` is the least `n` such that every graph on `n` vertices contains a
triangle or an independent set of size `5`. -/
