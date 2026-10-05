/-!
# No Clean Proved With Escape
Category: Proof-Carrying Apps (Lean)
Target: PCA.no_clean_proved_with_escape
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

section PCA

variable {P R : Type}

/-- A principal `c` can access resource `r` if `r` is in `c`'s scope, or `c` is
privileged, or `r` is unowned. -/

theorem no_clean_proved_with_escape
    (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (hclean : ∀ c r, canAccess inScope isPriv isUnowned c r → inScope c r)
    (hescape : ∃ c r, ¬ inScope c r ∧ (isPriv c ∨ isUnowned r)) : False := by
  obtain ⟨c, r, hns, hesc⟩ := hescape
  refine hns (hclean c r ?_)
  rcases hesc with hp | hu
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr hu)

end PCA

end PCA

