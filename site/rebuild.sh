#!/usr/bin/env bash
#
# Regenerate the deployable site from its sources:
#   * the Verso paper website   (site/verso/_site)   <- site/verso/Paper/*.lean
#   * the leanblueprint          (site/blueprint/web) <- site/blueprint/src/*.tex
#
# Run this after editing those sources, then review and commit:
#   git add site/ && git commit -m "site: regenerate" && git push severini main:main
#
# Usage:  ./site/rebuild.sh            (both)
#         ./site/rebuild.sh verso      (verso only)
#         ./site/rebuild.sh blueprint  (blueprint only)
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
what="${1:-all}"

build_verso() {
  echo "==> Verso paper website (site/verso)"
  ( cd "$ROOT/site/verso" \
      && lake build \
      && lake exe generate-paper --output _site )
  echo "    -> site/verso/_site regenerated"
}

build_blueprint() {
  echo "==> Blueprint (site/blueprint)"
  if command -v plastex >/dev/null 2>&1; then
    ( cd "$ROOT/site/blueprint/src" \
        && plastex -c plastex.cfg --dir=../web web.tex )
    echo "    -> site/blueprint/web regenerated"
  else
    echo "    !! plastex not found — skipping the blueprint."
    echo "       install: pip install plastex plastexdepgraph leanblueprint   (and Graphviz)"
    return 1
  fi
}

case "$what" in
  verso)     build_verso ;;
  blueprint) build_blueprint ;;
  all)       build_verso; build_blueprint || true ;;
  *) echo "usage: $0 [verso|blueprint|all]"; exit 2 ;;
esac

echo
echo "Done. Review and commit the regenerated HTML:"
echo "  git add site/ && git commit -m 'site: regenerate' && git push severini main:main"
