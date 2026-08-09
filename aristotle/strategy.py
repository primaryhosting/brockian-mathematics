"""strategy.py — prompt-strategy diversification for repeated attempts.

night_submit round-robins targets and re-sends them; identical prompts waste retries
(same input → similar output). This varies the approach per attempt number so each
re-attack of a target tries a genuinely different tactic, raising the odds Aristotle
(stochastic) finds a proof.
"""

STRATEGIES = [
    "",  # attempt 0: plain
    "Hint: try induction (or strong/structural induction) on the principal variable.",
    "Hint: search Mathlib for an existing lemma (exact?/apply?/rw?) that closes or nearly closes this; cite it.",
    "Hint: introduce and prove a key intermediate lemma first, then finish the goal from it.",
    "Hint: try heavy automation — aesop, omega, decide, norm_num, polyrith, nlinarith — on the residual goals.",
    "Hint: unfold definitions and reduce to a concrete finite/decidable computation where possible.",
    "Hint: reformulate to the contrapositive or an equivalent statement that is easier to attack.",
    "Hint: split into cases on the relevant hypothesis and discharge each branch separately.",
]


def pick(attempt: int) -> str:
    """Strategy hint for the (attempt)-th try of a target (0-indexed)."""
    if attempt <= 0:
        return ""
    return STRATEGIES[attempt % len(STRATEGIES)]
