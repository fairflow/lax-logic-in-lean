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
#   <site>/curry-paper/        CurryPaper (and /single/)
#   <site>/tools/*.html        the self-contained HTML explorers from docs/
#   <site>/drafts/             the Belief draft (PDF and landing page)
#
#   scripts/ci-papers.sh <site-dir> [part...]
#
# With no parts, everything above is built.  Parts select a subset, each
# replacing only its own directory: clp-paper, lax-paper, curry-paper (a Verso
# build of that paper alone; Lake builds just the library modules it imports),
# and extras (tools/ and drafts/, copies and pandoc only, no Lean).  The
# per-paper workflow (.github/workflows/paper-pages.yml) uses this to
# republish one paper on top of the last deployed site.
#
# HTML only.  The PDFs need a TeX installation (scripts/verso-tex-pdf.sh) and
# stay local: scripts/clp-paper.sh.
set -euo pipefail
site=$1
shift
parts=${*:-clp-paper lax-paper curry-paper extras}
want() { case " $parts " in *" $1 "*) return 0;; *) return 1;; esac; }
for p in $parts; do
  case $p in clp-paper|lax-paper|curry-paper|extras) ;; *) echo "ci-papers: unknown part $p"; exit 2;; esac
done
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

want clp-paper && build CLPPaper CLPPaperMain.lean clp-paper
want lax-paper && build LaxPaper LaxPaperMain.lean lax-paper
want curry-paper && build CurryPaper CurryPaperMain.lean curry-paper
want extras || exit 0

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
# Its companion, on keeping long agent work on course; marked DRAFT in its own
# text, so it carries the banner.
scripts/tutorial-html.py docs/claude-techniques.md "$site/tools/claude-techniques.html" --draft

# Paper drafts, published for comment under /drafts/.  A draft is published
# only by naming it here; the Verso papers above are the route for a finished
# paper.  The Belief draft was switched on at Matthew's word, 2026-10-11: the
# tracked PDF built from `paper/` (the working master since 2026-07-19), with a
# landing page carrying the DRAFT banner.  `docs/belief-paper-draft.md` is the
# superseded revision 2 and is NOT published.
mkdir -p "$site/drafts"
cp paper/belief.pdf "$site/drafts/belief-in-lax-logic.pdf"
scripts/tutorial-html.py docs/belief-draft.md "$site/drafts/belief-in-lax-logic.html" --draft
