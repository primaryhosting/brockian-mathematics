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


@[simp] lemma cntb_zero (P : Fin m → Prop) : cntb P 0 = 0 := by
  have h0 : {v : Fin m | P v ∧ (v : ℕ) < 0} = ∅ := by
    ext v; simp
  simp only [cntb, cnt, h0, Set.ncard_empty]

