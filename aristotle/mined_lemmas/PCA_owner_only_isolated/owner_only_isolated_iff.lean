/-!
# Owner Only Isolated
Category: Proof-Carrying Apps (Lean)
Target: PCA.owner_only_isolated
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

section PCA

variable {P R : Type}

/-- A principal `c` can access a resource `r` when `r` is in `c`'s scope, or `c` is
privileged, or `r` is unowned. -/

theorem owner_only_isolated_iff (ownerOf : R → P) (c : P) (r : R) :
    canAccess (fun c r => ownerOf r = c) (fun _ => False) (fun _ => False) c r ↔
      ownerOf r = c :=
  ⟨owner_only_isolated ownerOf c r, fun h => Or.inl h⟩

end PCA

end PCA

