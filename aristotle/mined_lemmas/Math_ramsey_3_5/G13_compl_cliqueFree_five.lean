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

theorem G13_compl_cliqueFree_five : G13ᶜ.CliqueFree 5 := by
  intro S hS
  obtain ⟨a, b, c, d, e, ha, hb, hc, hd, he, hab, hbc, hcd, hde⟩ := exists_sorted_five S hS.2
  have hclique := hS.1
  have key : ∀ {x y : Fin 13}, x ∈ (S : Set (Fin 13)) → y ∈ (S : Set (Fin 13)) → x < y →
      ¬ G13.Adj x y := fun hx hy hxy =>
    ((SimpleGraph.compl_adj _ _ _).1 (hclique hx hy (ne_of_lt hxy))).2
  exact G13_no_indep_five a b c d e hab hbc hcd hde
    ⟨key ha hb hab, key ha hc (hab.trans hbc), key ha hd (hab.trans (hbc.trans hcd)),
     key ha he (hab.trans (hbc.trans (hcd.trans hde))), key hb hc hbc,
     key hb hd (hbc.trans hcd), key hb he (hbc.trans (hcd.trans hde)), key hc hd hcd,
     key hc he (hcd.trans hde), key hd he hde⟩

