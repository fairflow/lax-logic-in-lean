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
