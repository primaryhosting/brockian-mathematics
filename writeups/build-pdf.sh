#!/bin/zsh
# build-pdf.sh — render a Markdown writeup to a clean academic PDF.
# Usage: ./build-pdf.sh <file.md> [Author] [Date]
# Toolchain: pandoc + tectonic (self-contained LaTeX; auto-fetches packages).
set -e
export PATH="/opt/homebrew/bin:$PATH"
MD="${1:?usage: build-pdf.sh <file.md> [author] [date]}"
AUTHOR="${2:-Riemann Labs}"
DATE="${3:-$(/bin/date +%Y-%m-%d)}"
OUT="${MD%.md}.pdf"
# Title = first level-1 heading, stripped of markdown.
TITLE="$(grep -m1 '^# ' "$MD" | sed 's/^# *//; s/[*_`]//g')"
[ -z "$TITLE" ] && TITLE="$(basename "${MD%.md}")"

# Normalize common Unicode math to LaTeX so the default (Latin Modern) font renders cleanly.
TMP="$(/usr/bin/mktemp -t writeup).md"
sed -e 's/≥/$\\geq$/g' -e 's/≤/$\\leq$/g' -e 's/≠/$\\neq$/g' \
    -e 's/×/$\\times$/g' -e 's/·/$\\cdot$/g' -e 's/≈/$\\approx$/g' \
    -e 's/⇒/$\\Rightarrow$/g' -e 's/⇔/$\\iff$/g' -e 's/→/$\\to$/g' \
    -e 's/∑/$\\sum$/g' -e 's/∈/$\\in$/g' -e 's/√/$\\surd$/g' \
    -e 's/ℤ/$\\mathbb{Z}$/g' -e 's/ℝ/$\\mathbb{R}$/g' -e 's/ℂ/$\\mathbb{C}$/g' -e 's/ℕ/$\\mathbb{N}$/g' \
    -e 's/ℵ/$\\aleph$/g' -e 's/λ/$\\lambda$/g' -e 's/γ/$\\gamma$/g' -e 's/σ/$\\sigma$/g' \
    -e 's/μ/$\\mu$/g' -e 's/π/$\\pi$/g' -e 's/ω/$\\omega$/g' -e 's/ε/$\\varepsilon$/g' \
    -e 's/₀/$_0$/g' -e 's/²/\\textsuperscript{2}/g' -e 's/³/\\textsuperscript{3}/g' \
    "$MD" > "$TMP"

pandoc "$TMP" \
  --from=markdown+tex_math_dollars+backtick_code_blocks+pipe_tables \
  --pdf-engine=tectonic \
  --metadata title="$TITLE" \
  --metadata author="$AUTHOR" \
  --metadata date="$DATE" \
  --toc --toc-depth=2 \
  --number-sections \
  -V geometry:"margin=1in" \
  -V fontsize=11pt \
  -V linkcolor=blue -V urlcolor=blue -V colorlinks=true \
  -V mainfont= \
  --highlight-style=tango \
  -o "$OUT"
echo "wrote $OUT ($(du -h "$OUT" | cut -f1))"
rm -f "$TMP"
