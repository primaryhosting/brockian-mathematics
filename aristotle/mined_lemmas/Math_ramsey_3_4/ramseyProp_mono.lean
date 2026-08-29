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
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Math

open Finset

/-- `RamseyProp n s t` says: every simple graph on `n` vertices contains either a clique of
size `s` or an independent set (a clique in the complement) of size `t`. -/

lemma ramseyProp_mono {m n s t : ℕ} (hmn : m ≤ n) (H : RamseyProp m s t) : RamseyProp n s t := by
  intro G
  let f : Fin m ↪ Fin n := Fin.castLEEmb hmn
  rcases H (SimpleGraph.comap f G) with ⟨S, hS⟩ | ⟨T, hT⟩
  · exact Or.inl ⟨S.map f, clique_map f G s S hS⟩
  · refine Or.inr ⟨T.map f, clique_map f Gᶜ t T ?_⟩
    rw [comap_compl]
    exact hT

end Mono

/-! ## R(3,3) ≤ 6 -/

section R33

variable {V : Type*} [DecidableEq V]

/-- Ramsey's theorem for `(3,3)`: any six vertices contain a triangle or an independent
triple. -/
