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


lemma cntb_full (P : Fin m → Prop) : cntb P m = cnt P := by
  have : {v : Fin m | P v ∧ (v : ℕ) < m} = {v : Fin m | P v} := by
    ext v; simp
  simp only [cntb, cnt, this]

/-- If `P` has at most as many elements as `P ∧ Q`, then `P` implies `Q`. -/
