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


lemma walkY_reach (i c j c' : Fin (m + 2)) :
    ∀ (K : ℕ) (w : Fin m) (kf : Fin (m + 2)), (kf : ℕ) = K → RS r s x K w →
      Relation.ReflTransGen ((cmach r s t).Step x)
        (St.walkY i c j c' s 0) (St.walkY i c j c' w kf) := by
  intro K
  induction K with
  | zero =>
      intro w kf hkf hw
      have h1 : w = s := hw
      have h2 : kf = 0 := Fin.ext (by rw [hkf, val_zero'])
      rw [h1, h2]
  | succ K ih =>
      intro w kf hkf hw
      obtain ⟨u, hu, hstep⟩ := hw
      have hKlt : K < m + 2 := by omega
      have hpath := ih u ⟨K, hKlt⟩ rfl hu
      exact hpath.tail (stepT3 r s t x i c j c' ⟨K, hKlt⟩ kf u w (by rw [hkf]) hstep)

/-- The same for the walks used in negative certificates. -/
