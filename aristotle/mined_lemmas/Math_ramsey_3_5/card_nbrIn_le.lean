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

theorem card_nbrIn_le {A : Finset V} {v : V} {t : ℕ} (hv : v ∈ A)
    (htri : ¬ HasTriangleIn G A) (hind : ¬ HasIndepIn G A (t + 1)) :
    (nbrIn G A v).card ≤ t := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (n := t + 1) hlt
  refine hind ⟨S, hS.trans (Finset.filter_subset _ _), hcard, ?_⟩
  intro x hx y hy hxy hadj
  have hx' := hS hx
  have hy' := hS hy
  simp only [nbrIn, Finset.mem_filter] at hx' hy'
  exact htri ⟨v, hv, x, hx'.1, y, hy'.1, (G.ne_of_adj hx'.2), (G.ne_of_adj hy'.2), hxy,
    hx'.2, hy'.2, hadj⟩

/-- The set of non-neighbours of `v` contains no triangle and no independent set of size `t`
(the latter would extend by `v`), so it is smaller than `R(3,t)`. -/
