/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 4

We define the two-colour Ramsey number `Math.ramseyNumber` and prove `R(3,4) = 9`.
-/

open Finset SimpleGraph

namespace Math

/-- `Arrows n r s` says that every simple graph on `n` vertices contains either a clique of
size `r` or an independent set of size `s`, i.e. `n → (r, s)` in Ramsey arrow notation. -/

theorem arrows_mono {m n r s : ℕ} (hmn : m ≤ n) (h : Arrows m r s) : Arrows n r s := by
  intro G
  rcases h (G.comap (Fin.castLEEmb hmn)) with ⟨A, hA⟩ | ⟨B, hB⟩
  · exact Or.inl ⟨A.map (Fin.castLEEmb hmn), isNClique_map_comap G _ hA⟩
  · exact Or.inr ⟨B.map (Fin.castLEEmb hmn), isNIndepSet_map_comap G _ hB⟩

/-! ### Small constructions of independent sets -/

