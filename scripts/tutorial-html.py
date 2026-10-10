#!/usr/bin/env python3
"""Render `docs/github-with-claude-tutorial.md` as one self-contained HTML page.

    scripts/tutorial-html.py <in.md> <out.html>

Needs `pandoc` on PATH.  Used by `scripts/ci-papers.sh`, so the page on the
Pages site is generated from the tracked Markdown at build time and cannot
drift from it.  The Markdown is the source; do not edit the HTML.
"""
import re
import subprocess
import sys

CSS = """
:root{--bg:#f6f7f6;--surface:#fff;--fg:#1d2422;--muted:#5b6662;--rule:#d9dfdc;
  --accent:#1f6f5c;--code-bg:#eef1ef;
  --display:"Literata",Georgia,"Times New Roman",serif;
  --body:"Source Sans 3",-apple-system,"Segoe UI",Helvetica,Arial,sans-serif;
  --mono:"JetBrains Mono",ui-monospace,SFMono-Regular,Menlo,monospace}
@media (prefers-color-scheme: dark){:root{--bg:#121715;--surface:#18201d;
  --fg:#e3e9e6;--muted:#9aa7a2;--rule:#2c3632;--accent:#6cc3a8;--code-bg:#1e2724;
  color-scheme:dark}}
html{-webkit-text-size-adjust:100%}
body{margin:0;background:var(--bg);color:var(--fg);font:17px/1.6 var(--body);
  padding:24px 16px 64px}
.wrap{max-width:42rem;margin:0 auto}
header h1{font:650 clamp(1.7rem,5vw,2.4rem)/1.15 var(--display);text-wrap:balance;margin:0 0 .4em}
header .meta{color:var(--muted);font-size:.95rem}
details.toc{position:sticky;top:0;z-index:2;background:var(--surface);
  border:1px solid var(--rule);border-radius:8px;padding:.55rem .9rem;margin:1rem 0}
details.toc summary{cursor:pointer;font-weight:600;color:var(--accent)}
details.toc ol{margin:.5rem 0 .2rem;padding-left:1.3rem}
details.toc a{color:var(--fg);text-decoration:none}
details.toc a:hover,details.toc a:focus-visible{color:var(--accent);text-decoration:underline}
h2{font:650 1.45rem/1.25 var(--display);text-wrap:balance;margin:2.2rem 0 .6rem;
  padding-left:.9rem;border-left:3px solid var(--accent);scroll-margin-top:4.5rem}
h3{font:600 1.12rem/1.3 var(--body);margin:1.6rem 0 .4rem;color:var(--accent);scroll-margin-top:4.5rem}
p,li{max-width:65ch} ul,ol{padding-left:1.25rem} li{margin:.3rem 0}
strong{font-weight:600} a{color:var(--accent)}
code{font:400 .86em var(--mono);background:var(--code-bg);padding:.08em .32em;
  border-radius:4px;overflow-wrap:anywhere}
pre{background:var(--code-bg);padding:.8rem 1rem;border-radius:6px;overflow-x:auto}
pre code{background:none;padding:0;overflow-wrap:normal}
hr{border:0;border-top:1px solid var(--rule);margin:2rem 0}
footer{margin-top:2.5rem;color:var(--muted);font-size:.9rem;border-top:1px solid var(--rule);padding-top:1rem}
:focus-visible{outline:2px solid var(--accent);outline-offset:2px}
"""

FONTS = ("https://fonts.googleapis.com/css2?family=Literata:opsz,wght@7..72,500;7..72,650"
         "&family=Source+Sans+3:ital,wght@0,400;0,600;1,400"
         "&family=JetBrains+Mono:wght@400;500&display=swap")


def main() -> int:
    src, out = sys.argv[1], sys.argv[2]
    body = subprocess.run(["pandoc", src, "-f", "gfm", "-t", "html5"],
                          check=True, capture_output=True, text=True).stdout
    body = re.sub(r"<h([1-6])\s+id=", r"<h\1 id=", body)
    m = re.search(r"<h1[^>]*>(.*?)</h1>", body, flags=re.S)
    title = re.sub(r"\s+", " ", m.group(1)) if m else "Working guide"
    body = body.replace(m.group(0), "", 1) if m else body
    intro, rest = body, ""
    if "<p>Contents</p>" in body and "<hr />" in body:
        intro, rest = body.split("<p>Contents</p>", 1)
        rest = rest.split("<hr />", 1)[1]
    heads = re.findall(r'<h2 id="([^"]+)">(.*?)</h2>', rest, flags=re.S)
    toc = "".join(f'<li><a href="#{i}">{re.sub(chr(92) + "s+", " ", t)}</a></li>'
                  for i, t in heads)
    page = f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{re.sub(r"<[^>]+>", "", title)}</title>
<link rel="stylesheet" href="{FONTS}">
<style>{CSS}</style></head><body><div class="wrap">
<header><h1>{title}</h1><div class="meta">{intro.strip()}</div></header>
<details class="toc"><summary>Contents</summary><ol>{toc}</ol></details>
<main>{rest}</main>
<footer>Generated from <code>docs/github-with-claude-tutorial.md</code> in
<a href="https://github.com/fairflow/lax-logic-in-lean">fairflow/lax-logic-in-lean</a>.
<a href="../">Back to the Blueprint.</a></footer>
</div></body></html>
"""
    open(out, "w", encoding="utf-8").write(page)
    print(f"tutorial-html: {out} ({len(heads)} sections)")
    return 0 if heads else 1


if __name__ == "__main__":
    sys.exit(main())
