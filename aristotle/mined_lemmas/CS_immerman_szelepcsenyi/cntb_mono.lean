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


lemma cntb_mono (P : Fin m → Prop) {J J' : ℕ} (h : J ≤ J') : cntb P J ≤ cntb P J' := by
  simp only [cntb, cnt]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro v ⟨h1, h2⟩
  exact ⟨h1, by omega⟩

