import Mathlib
import RequestProject.Main

/-!
# Mathlib-flavoured corollary of `with_check_true_admits_forge`

`RequestProject/Main.lean` must begin with a mandated module doc comment, which
forces that module to be import-free (Lean rejects `import` after a doc comment).
This companion module imports Mathlib and restates the main result in terms of
the *set* of admitted forgeries.
-/

set_option autoImplicit false

namespace PCA
namespace WriteIntegrity

/-- The set of requests that the engine admits even though they are forged. -/

theorem trivialEngine_not_sound_ownership :
    ¬ Sound trivialEngine (fun p k => p = k) :=
  (with_check_true_admits_forge trivialEngine (fun _ => rfl) (fun p k => p = k)
    ⟨0, 1, by decide⟩).2

end WriteIntegrity
end PCA

#print axioms PCA.WriteIntegrity.with_check_true_admits_forge

