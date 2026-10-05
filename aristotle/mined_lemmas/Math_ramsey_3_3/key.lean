/-
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxRecDepth 10000

namespace Math


private theorem key : ∀ b01 b02 b03 b04 b05 b12 b13 b14 b15 b23 b24 b25 b34 b35 b45 : Bool,
    (((b01 == b02) && (b02 == b12)) ||
    (((b01 == b03) && (b03 == b13)) ||
    (((b01 == b04) && (b04 == b14)) ||
    (((b01 == b05) && (b05 == b15)) ||
    (((b02 == b03) && (b03 == b23)) ||
    (((b02 == b04) && (b04 == b24)) ||
    (((b02 == b05) && (b05 == b25)) ||
    (((b03 == b04) && (b04 == b34)) ||
    (((b03 == b05) && (b05 == b35)) ||
    (((b04 == b05) && (b05 == b45)) ||
    (((b12 == b13) && (b13 == b23)) ||
    (((b12 == b14) && (b14 == b24)) ||
    (((b12 == b15) && (b15 == b25)) ||
    (((b13 == b14) && (b14 == b34)) ||
    (((b13 == b15) && (b15 == b35)) ||
    (((b14 == b15) && (b15 == b45)) ||
    (((b23 == b24) && (b24 == b34)) ||
    (((b23 == b25) && (b25 == b35)) ||
    (((b24 == b25) && (b25 == b45)) ||
    (((b34 == b35) && (b35 == b45)))))))))))))))))))))) = true := by decide

/-- Every 2-colouring of the edges of `K₆` contains a monochromatic triangle. -/
