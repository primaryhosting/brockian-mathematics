import Mathlib
namespace Brockian.GraphAcyclic

/-- Twin-admissible residue: both a and a+2 are units mod n. -/

lemma side_invariant (g : V → ℤ) (hinj : Function.Injective g) {a b : V} (h1 : g b = g a + 1)
    {H : SimpleGraph V} (hstep : ∀ ⦃u v : V⦄, H.Adj u v → g v = g u + 1 ∨ g v = g u - 1)
    {x y : V} (p : H.Walk x y) (hp : s(a, b) ∉ p.edges) : g x ≤ g a ↔ g y ≤ g a := by
  induction p with
  | nil => simp
  | @cons u v w hd tail IH =>
    rw [Walk.edges_cons] at hp
    simp at hp
    have IH' := IH hp.2
    have hp_ne := hp.1
    have huv_step : g u ≤ g a ↔ g v ≤ g a := by
      rcases hstep hd with hv | hv
      · -- `g v = g u + 1`: crossing the level would force the edge to be `s(a, b)`
        constructor
        · intro hu
          by_contra hna
          push_neg at hna
          have hu_eq : u = a := hinj (by linarith : g u = g a)
          have hv_eq : v = b := hinj (by rw [hv, hu_eq, h1])
          exact hp_ne.1 hu_eq.symm hv_eq.symm
        · intro hv_le
          linarith
      · -- `g v = g u - 1`: crossing the level would force the edge to be `s(b, a)`
        constructor
        · intro hu
          linarith
        · intro hv_le
          by_contra hna
          push_neg at hna
          have hu_eq : u = b := hinj (by linarith : g u = g b)
          have hv_eq : v = a := hinj (by linarith : g v = g a)
          exact hp_ne.2 hv_eq.symm hu_eq.symm
    rw [huv_step, IH']

/-- With an injective height function as above, every edge is a bridge. -/
