/-
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- `Omega n` is the number of prime factors of `n`, counted with multiplicity
(the classical arithmetic function `Ω`). -/

def Omega (n : ℕ) : ℕ := n.primeFactorsList.length

/-- `n` is a *Chen sum* if `n = p + q` with `p` prime and `q` having at most two
prime factors (counted with multiplicity). -/
