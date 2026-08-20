import Mathlib
namespace Brockian.GraphAcyclic

/-- Twin-admissible residue: both a and a+2 are units mod n. -/

theorem acyclic_of_int_height (g : V → ℤ) (hinj : Function.Injective g)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → g y = g x + 1 ∨ g y = g x - 1) :
    G.IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro v w hvw
  rcases hstep hvw with h | h
  · exact isBridge_of_int_height g hinj hstep hvw h
  · have := isBridge_of_int_height g hinj hstep hvw.symm (by linarith)
    rwa [Sym2.eq_swap] at this

end Height

section Arith

variable {M : ℕ} [NeZero M]

omit [NeZero M] in
/-- `3` is invertible mod `M` when `gcd(3, M) = 1`. -/
