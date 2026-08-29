/-
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- A family `S` of sets is a *sunflower with core `c`* if any two distinct members of `S`
intersect exactly in `c`. -/

lemma hasSunflower_of_disjoint {F : Finset (Finset α)} {p : ℕ} {D : Finset (Finset α)}
    (hDF : D ⊆ F) (hD : D.card = p) (hdisj : ∀ A ∈ D, ∀ B ∈ D, A ≠ B → Disjoint A B) :
    HasSunflower F p :=
  ⟨D, hDF, hD, ∅, fun A hA B hB hAB =>
    Finset.disjoint_iff_inter_eq_empty.mp (hdisj A hA B hB hAB)⟩

/-- **Reduction of the sunflower bound to the spread-to-disjoint property.**
If `rho` is nondecreasing in `k`, at least `p`, and has the spread-to-disjoint property, then
every family of at least `(rho p k) ^ k` sets of size `k` contains a sunflower with `p` petals. -/
