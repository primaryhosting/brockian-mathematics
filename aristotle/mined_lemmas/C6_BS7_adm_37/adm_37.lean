import Mathlib
namespace C6.BS7

theorem adm_37 (g : ZMod 37) (hg : g ≠ 0) :
    (Finset.univ.filter (fun r : ZMod 37 => r ≠ 0 ∧ r ≠ -g)).card = 35 := by
  have h1 : (Finset.univ.filter (fun r : ZMod 37 => r ≠ 0 ∧ r ≠ -g))
      = ({0, -g} : Finset (ZMod 37))ᶜ := by
    ext r; simp
  have h2 : ({0, -g} : Finset (ZMod 37)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa [eq_comm, neg_eq_zero] using hg),
      Finset.card_singleton]
  rw [h1, Finset.card_compl, h2]
  simp

/-- The admissible 12-tuple `{0,2,6,8,12,18,20,26,30,32,36,42}` has positive local factor at
every `p`: for `p ≥ 13` the number of occupied residues is at most the size `12` of the tuple,
and for `p ∈ {2,3,5,7,11}` admissibility is checked by computation. -/
