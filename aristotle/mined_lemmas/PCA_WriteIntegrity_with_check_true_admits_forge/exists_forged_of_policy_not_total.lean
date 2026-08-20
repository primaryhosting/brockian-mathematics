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

theorem exists_forged_of_policy_not_total
    (auth : Policy) (hgap : ∃ p k : Nat, ¬ auth p k) :
    ∃ r : Request, Forged auth r := by
  obtain ⟨p, k, hpk⟩ := hgap
  exact ⟨⟨p, k, 0⟩, hpk⟩

/-- An engine whose guard is constantly `true` admits every request. -/
