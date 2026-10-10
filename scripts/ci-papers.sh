#!/usr/bin/env bash
# Build the two Verso papers as HTML into subdirectories of the Pages site.
#
#   scripts/ci-papers.sh <site-dir>
#
# A repository has ONE GitHub Pages site, and every deploy replaces all of it.
# So the papers are not deployed separately: they are built into the same
# artifact as the Blueprint, under their own paths, and the Blueprint keeps the
# site root.  Result:
#
#   <site>/                    the Blueprint (scripts/ci-pages.sh, unchanged)
#   <site>/clp-paper/          CLPPaper, one page per section
#   <site>/clp-paper/single/   CLPPaper, one page
#   <site>/lax-paper/          LaxPaper, one page per section
#   <site>/lax-paper/single/   LaxPaper, one page
#   <site>/tools/*.html        the self-contained HTML explorers from docs/
#
# HTML only.  The PDFs need a TeX installation (scripts/verso-tex-pdf.sh) and
# stay local: scripts/clp-paper.sh.
set -euo pipefail
site=$1
cd "$(dirname "$0")/.."
test -f "$site/index.html" || { echo "ci-papers: $site has no index.html (build the Blueprint first)"; exit 1; }

build() {  # lib main slug
  local lib=$1 main=$2 slug=$3 out=_out/papers/$3
  lake build "$lib"
  rm -rf "$out"
  lake lean "$main" -- --run "$main" --output "$out" --with-html-single
  test -f "$out/html-multi/index.html"
  test -f "$out/html-single/index.html"
  rm -rf "${site:?}/$slug"
  mkdir -p "$site/$slug"
  cp -R "$out/html-multi/." "$site/$slug/"
  mkdir -p "$site/$slug/single"
  cp -R "$out/html-single/." "$site/$slug/single/"
  echo "ci-papers: $site/$slug/index.html"
}

build CLPPaper CLPPaperMain.lean clp-paper
build LaxPaper LaxPaperMain.lean lax-paper

# The explorers are tracked, self-contained pages (no local references), so they
# are copied as they are.  The list is explicit: a page is published only by
# naming it here.
mkdir -p "$site/tools"
for f in rn-catalogue rho-optables pll-calculus-ledger interpolation-guide principal-proof-states; do
  cp "docs/$f.html" "$site/tools/$f.html"
done
echo "ci-papers: $site/tools/ ($(ls "$site/tools" | wc -l | tr -d ' ') pages)"

# The working guide, rendered from its tracked Markdown at build time, so the
# page cannot drift from the source.  Needs pandoc (installed by the workflow).
scripts/tutorial-html.py docs/github-with-claude-tutorial.md "$site/tools/github-with-claude.html"
