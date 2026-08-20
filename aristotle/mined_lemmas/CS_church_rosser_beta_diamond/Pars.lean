/-!
# Church Rosser Beta Diamond
Category: Computer Science
Target: CS.church_rosser_beta_diamond
Statement: One-step parallel β-reduction in the λ-calculus has the diamond property.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/



namespace CS

/-- Untyped λ-terms in de Bruijn representation. -/
inductive Term where
  | var : Nat → Term
  | app : Term → Term → Term
  | lam : Term → Term

namespace Term

/-- Lifting of a renaming under a binder. -/

theorem Pars.confluent {a b c : Term} (hb : Pars a b) (hc : Pars a c) :
    ∃ d, Pars b d ∧ Pars c d := by
  induction hb generalizing c with
  | refl a => exact ⟨c, hc, .refl c⟩
  | @step a b₁ b h₁ _ ih =>
      obtain ⟨e, hb₁e, hce⟩ := Pars.strip h₁ hc
      obtain ⟨d, hbd, hed⟩ := ih hb₁e
      exact ⟨d, hbd, .step hce hed⟩

end Term

open Term in
/-- **Diamond property for one-step parallel β-reduction in the λ-calculus.**
If a λ-term `a` parallel-reduces in one step to both `b` and `c`, then `b` and `c`
have a common one-step parallel reduct `d`. -/
