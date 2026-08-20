import Mathlib
open Filter Topology
namespace MS2.Analysis2


theorem monotone_bounded_converges (s : ℕ → ℝ) (hm : Monotone s) (M : ℝ) (hb : ∀ n, s n ≤ M) :
    ∃ L, Tendsto s atTop (nhds L) :=
  ⟨_, tendsto_atTop_ciSup hm ⟨M, by rintro _ ⟨n, rfl⟩; exact hb n⟩⟩

/-- Rolle's theorem. The differentiability hypothesis `hd` is not needed for this
conclusion (Mathlib's `exists_deriv_eq_zero` only requires continuity: at a point where
`f` is not differentiable, `deriv f` is defined to be `0`), but it is kept as it was
part of the requested statement. -/
