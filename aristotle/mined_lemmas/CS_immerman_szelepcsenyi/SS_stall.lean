import RequestProject.ISMachine

/-!
# Completeness of the counting machine

If `t` is not reachable from `s`, then the counting machine has an accepting computation:
all the guesses it has to make are correct guesses, and all the certificates it has to
produce do exist.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS


lemma SS_stall (i : ℕ) (h : SS r s x i = SS r s x (i + 1)) :
    SS r s x (i + 1) = SS r s x (i + 2) := by
  have hmem : ∀ u, RS r s x i u ↔ RS r s x (i + 1) u := by
    intro u
    constructor
    · intro hu; exact (Set.ext_iff.mp h u).mp hu
    · intro hu; exact (Set.ext_iff.mp h u).mpr hu
  ext v
  simp only [SS, Set.mem_setOf_eq, RS_succ]
  constructor
  · rintro ⟨u, hu, hstep⟩; exact ⟨u, (hmem u).mp hu, hstep⟩
  · rintro ⟨u, hu, hstep⟩; exact ⟨u, (hmem u).mpr hu, hstep⟩

