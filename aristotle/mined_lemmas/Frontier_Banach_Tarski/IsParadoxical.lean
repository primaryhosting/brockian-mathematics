/-
Absorbing the countable set of poles: the unit sphere is `SO(3)`-paradoxical.
-/
import RequestProject.Sphere

open Matrix Set Pointwise

namespace BT

noncomputable section

/-! ### Countability of the solution sets of rotation equations -/

/-- For a point `d` off the `z`-axis, only countably many angles `t` satisfy
`rZ (c * t) • d = d'`. -/

theorem IsParadoxical.map {G' : Type*} [Group G'] [MulAction G' X] (F : G → G')
    (hF : ∀ (g : G) (x : X), F g • x = g • x) {A : Set X} (h : IsParadoxical G A) :
    IsParadoxical G' A := by
  obtain ⟨P, Q, hP, hQ, hPQ, hAP, hAQ⟩ := h
  exact ⟨P, Q, hP, hQ, hPQ, hAP.map F hF, hAQ.map F hF⟩

/-- **Absorption lemma**: if `rho` moves `D` off itself under all positive powers, and all the
powers `rho ^ n • D` stay inside `A`, then `A` is equidecomposable with `A \ D`. -/
