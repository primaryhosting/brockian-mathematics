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

theorem sph_diff_bad_invariant (w : F2) {x : E} (hx : x ∈ sph \ badSet) :
    phi w • x ∈ sph \ badSet := by
  refine ⟨smul_mem_sph _ hx.1, ?_⟩
  rintro ⟨-, v, hv, hvx⟩
  refine hx.2 ⟨hx.1, w⁻¹ * v * w, ?_, ?_⟩
  · intro hcon
    apply hv
    have : v = w * w⁻¹ := by
      have := congrArg (fun z => w * z * w⁻¹) hcon
      simpa [mul_assoc] using this
    simpa using this
  · rw [map_mul, map_mul, SemigroupAction.mul_smul, SemigroupAction.mul_smul, hvx, map_inv,
      inv_smul_smul]

