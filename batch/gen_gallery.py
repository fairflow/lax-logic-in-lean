import json, os, re, sys
def rd(p): return open(p, encoding='utf-8', errors='replace').read()
rows=[]
for line in rd('batch/results.tsv').split('\n'):
    p=line.rstrip('\n').split('\t')
    if len(p)<5: continue
    n,tag,f,v,ms = p[0],p[1],p[2],p[3],p[4]
    d=(p[5] if len(p)>5 else '').strip().replace('�','')
    rec={'n':n,'tag':tag,'f':f,'v':v,'ms':int(ms)}
    if d.startswith('term'): rec['term']=d[4:].strip()
    elif d.startswith('model'):
        m=re.search(r'(\d+) worlds .* minimised (\d+)', d)
        if m: rec['raw']=int(m.group(1)); rec['min']=int(m.group(2))
    for k in ('min','calc'):
        pth=f'batch/cell{n}.{k}.svg'
        if os.path.exists(pth): rec['svg_'+k]=rd(pth).strip()
    rows.append(rec)
d=rows
def esc(s): return s.replace('&','&amp;').replace('<','&lt;').replace('>','&gt;')
np=sum(1 for r in d if r['v']=='PROVED'); nr=sum(1 for r in d if r['v']=='REFUTED')
no=sum(1 for r in d if r['v'].startswith('TIMEOUT'))
diff=[r for r in d if r.get('raw') and r.get('min') and r['raw']!=r['min']]
# Rm usage: how many refuted cells need no non-reflexive Rm edge
def rmc(s): return len(re.findall(r'marker-end="url\(#aRm\)"', s or ''))
nofm=[r for r in d if 'svg_min' in r and rmc(r['svg_min'])==0]

head = '''<title>PLL Decider Batch</title>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Spectral:wght@400;600&family=IBM+Plex+Sans:wght@400;500;600&family=IBM+Plex+Mono:wght@400;500&display=swap">
<style>
:root{--ground:#F4F6F9;--surface:#FFF;--ink:#15181E;--muted:#5A6272;--line:#DBE0E8;
 --accent:#2266CC;--accent-soft:#E8EFFA;--proved:#12664A;--proved-bg:#E2F0EA;
 --refuted:#9E3520;--refuted-bg:#F8E7E2;--open:#7A5200;--open-bg:#F7EEDA;
 --shadow:0 1px 2px rgba(20,30,50,.06),0 4px 14px rgba(20,30,50,.05);}
@media (prefers-color-scheme:dark){:root:not([data-theme="light"]){
 --ground:#101318;--surface:#191D24;--ink:#E7EAEF;--muted:#98A1B2;--line:#2B313B;
 --accent:#7FB0F5;--accent-soft:#1B2634;--proved:#7FD3B0;--proved-bg:#142A22;
 --refuted:#F0A08C;--refuted-bg:#2E1A15;--open:#E5C179;--open-bg:#2C2415;
 --shadow:0 1px 2px rgba(0,0,0,.4),0 4px 14px rgba(0,0,0,.3);}}
:root[data-theme="dark"]{--ground:#101318;--surface:#191D24;--ink:#E7EAEF;--muted:#98A1B2;
 --line:#2B313B;--accent:#7FB0F5;--accent-soft:#1B2634;--proved:#7FD3B0;--proved-bg:#142A22;
 --refuted:#F0A08C;--refuted-bg:#2E1A15;--open:#E5C179;--open-bg:#2C2415;
 --shadow:0 1px 2px rgba(0,0,0,.4),0 4px 14px rgba(0,0,0,.3);}
*{box-sizing:border-box}
body{margin:0;background:var(--ground);color:var(--ink);
 font-family:"IBM Plex Sans",system-ui,-apple-system,sans-serif;font-size:15px;line-height:1.55}
.wrap{max-width:1180px;margin:0 auto;padding:38px 22px 70px}
h1{font-family:Spectral,Georgia,serif;font-weight:600;font-size:2.1rem;margin:0 0 6px;
 letter-spacing:-.01em;text-wrap:balance}
.sub{color:var(--muted);max-width:66ch;margin:0 0 26px}
.mono,.f,.detail,.cf,.term{font-family:"IBM Plex Mono","DejaVu Sans Mono",ui-monospace,monospace}
.stats{display:flex;flex-wrap:wrap;gap:10px;margin-bottom:12px}
.stat{background:var(--surface);border:1px solid var(--line);border-radius:8px;
 padding:12px 18px;min-width:112px;box-shadow:var(--shadow)}
.stat b{display:block;font-size:1.85rem;line-height:1.1;font-variant-numeric:tabular-nums;
 font-family:Spectral,Georgia,serif;font-weight:600}
.stat span{font-size:.74rem;text-transform:uppercase;letter-spacing:.07em;color:var(--muted)}
.s-p b{color:var(--proved)}.s-r b{color:var(--refuted)}.s-o b{color:var(--open)}
.note{background:var(--accent-soft);border-left:3px solid var(--accent);padding:12px 16px;
 border-radius:0 6px 6px 0;margin:20px 0 28px;font-size:.92rem;max-width:80ch}
h2{font-family:Spectral,Georgia,serif;font-weight:600;font-size:1.32rem;margin:40px 0 6px;
 padding-top:14px;border-top:1px solid var(--line)}
.h2sub{color:var(--muted);font-size:.9rem;margin:0 0 18px;max-width:74ch}
.filters{display:flex;flex-wrap:wrap;gap:7px;margin-bottom:16px}
.filters button{font:inherit;font-size:.83rem;padding:5px 13px;border-radius:20px;cursor:pointer;
 border:1px solid var(--line);background:var(--surface);color:var(--muted)}
.filters button[aria-pressed="true"]{background:var(--accent);border-color:var(--accent);color:#fff}
.filters button:focus-visible{outline:2px solid var(--accent);outline-offset:2px}
.tablewrap{overflow-x:auto;background:var(--surface);border:1px solid var(--line);
 border-radius:10px;box-shadow:var(--shadow)}
table{border-collapse:collapse;width:100%;font-size:.88rem}
th{text-align:left;font-size:.72rem;text-transform:uppercase;letter-spacing:.07em;color:var(--muted);
 font-weight:600;padding:11px 14px;border-bottom:1px solid var(--line);position:sticky;top:0;
 background:var(--surface)}
td{padding:9px 14px;border-bottom:1px solid var(--line);vertical-align:top}
tr:last-child td{border-bottom:none}
td.num{color:var(--muted);font-variant-numeric:tabular-nums;width:44px}
td.ms{text-align:right;font-variant-numeric:tabular-nums;color:var(--muted);white-space:nowrap}
td.tag{color:var(--muted);white-space:nowrap;font-size:.8rem}
td.f{font-size:.9rem}
td.detail{font-size:.8rem;color:var(--muted);max-width:330px;overflow-wrap:anywhere}
.pill{display:inline-block;font-size:.7rem;font-weight:600;letter-spacing:.05em;padding:3px 9px;
 border-radius:11px;white-space:nowrap;text-transform:uppercase}
.PROVED{background:var(--proved-bg);color:var(--proved)}
.REFUTED{background:var(--refuted-bg);color:var(--refuted)}
.TIMEOUT{background:var(--open-bg);color:var(--open)}
.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(340px,1fr));gap:16px}
.card{background:var(--surface);border:1px solid var(--line);border-radius:10px;overflow:hidden;
 box-shadow:var(--shadow);display:flex;flex-direction:column}
.card header{padding:13px 15px 11px;border-bottom:1px solid var(--line)}
.card .cf{font-size:.93rem;overflow-wrap:anywhere;margin-bottom:7px}
.meta{display:flex;align-items:center;gap:9px;flex-wrap:wrap;font-size:.75rem;color:var(--muted)}
.pic{background:#fff;padding:8px;overflow-x:auto;min-height:90px}
.pic svg{display:block;max-width:100%;height:auto}
.toggle{display:flex;border-top:1px solid var(--line)}
.toggle button{flex:1;font:inherit;font-size:.76rem;padding:7px;border:none;cursor:pointer;
 background:var(--surface);color:var(--muted);border-right:1px solid var(--line)}
.toggle button:last-child{border-right:none}
.toggle button[aria-pressed="true"]{background:var(--accent-soft);color:var(--accent);font-weight:600}
.toggle button:focus-visible{outline:2px solid var(--accent);outline-offset:-2px}
.legend{display:flex;gap:20px;flex-wrap:wrap;font-size:.82rem;color:var(--muted);margin:0 0 16px;
 align-items:center}
.legend i{display:inline-block;width:26px;height:0;vertical-align:middle;margin-right:6px}
.li-le{border-top:2px dashed #999}.li-rm{border-top:2px solid var(--accent)}
.dot{display:inline-block;width:11px;height:11px;border-radius:50%;border:2px solid #333;
 vertical-align:middle;margin-right:6px;background:#fff}
.dot.fal{background:#333}
footer{margin-top:44px;padding-top:18px;border-top:1px solid var(--line);color:var(--muted);
 font-size:.82rem;max-width:80ch}
code{font-family:"IBM Plex Mono","DejaVu Sans Mono",ui-monospace,monospace;
 background:var(--accent-soft);padding:1px 5px;border-radius:4px;font-size:.86em}
@media (prefers-reduced-motion:reduce){*{transition:none!important;animation:none!important}}
</style>'''

rowsH=[]
for r in d:
    cls='TIMEOUT' if r['v'].startswith('TIMEOUT') else r['v']
    lbl='undecided' if cls=='TIMEOUT' else r['v'].lower()
    if 'term' in r: det=esc(r['term'])
    elif r.get('raw'): det=f"{r['raw']} worlds &rarr; {r['min']} minimised"
    else: det='&mdash;'
    nv=r['tag'].split()[0]
    rowsH.append(f'<tr data-v="{cls}" data-nv="{nv}"><td class="num">{r["n"]}</td>'
      f'<td class="tag">{esc(r["tag"])}</td><td class="f">{esc(r["f"])}</td>'
      f'<td><span class="pill {cls}">{lbl}</span></td><td class="ms">{r["ms"]}&thinsp;ms</td>'
      f'<td class="detail">{det}</td></tr>')

cards=[];svgmap={}
for r in d:
    if 'svg_min' not in r: continue
    n=r['n']
    svgmap[n]={'min':r['svg_min'],'calc':r.get('svg_calc','')}
    differs=r.get('raw') and r.get('min') and r['raw']!=r['min']
    tog=''
    if differs and r.get('svg_calc'):
        tog=(f'<div class="toggle"><button aria-pressed="true" data-k="min" data-n="{n}">'
             f'minimised &middot; {r["min"]}</button>'
             f'<button aria-pressed="false" data-k="calc" data-n="{n}">'
             f'from the calculus &middot; {r["raw"]}</button></div>')
    wc=(f'{r["raw"]} &rarr; {r["min"]} worlds' if differs
        else (f'{r.get("min","?")} worlds' if r.get('min') else ''))
    norm = ' &middot; no R<sub>m</sub>' if rmc(r['svg_min'])==0 else ''
    cards.append(f'''<article class="card" data-nv="{r['tag'].split()[0]}">
<header><div class="cf">{esc(r['f'])}</div>
<div class="meta"><span class="pill REFUTED">refuted</span><span>{wc}{norm}</span>
<span>{r['ms']}&thinsp;ms</span></div></header>
<div class="pic" id="pic{n}">{r['svg_min']}</div>{tog}</article>''')

# JSON in a script tag: escape "</" so the parser cannot see a closing tag
sj=json.dumps(svgmap, ensure_ascii=False).replace('</','<\\/')

body=f'''<div class="wrap">
<h1>PLL Decider Batch</h1>
<p class="sub">{len(d)} formulas through <span class="mono">lake&nbsp;exe&nbsp;pll</span> — the untrusted W-engine, the verified <span class="mono">checkClosed</span> certificate, then <span class="mono">decideOfStore</span>. Ten seconds per cell. Proved cells carry a <span class="mono">Tm</span> proof term; refuted cells carry a minimised Kripke countermodel, drawn below.</p>
<div class="stats">
<div class="stat s-p"><b>{np}</b><span>proved</span></div>
<div class="stat s-r"><b>{nr}</b><span>refuted</span></div>
<div class="stat s-o"><b>{no}</b><span>undecided</span></div>
<div class="stat"><b>{len(d)}</b><span>cells</span></div>
<div class="stat"><b>{len(diff)}</b><span>views differ</span></div>
<div class="stat"><b>{len(nofm)}</b><span>no R<sub>m</sub> needed</span></div>
</div>
<p class="note">Every verdict is certified in-process: the engine's store passed <span class="mono">checkClosed</span>, whose soundness theorem pins <span class="mono">[propext, Quot.sound]</span>. Undecided means <em>not-closed-within-bound</em> at this budget — a frontier marker, never a verdict about the formula. Proof terms print de&nbsp;Bruijn indices bare; <span class="mono">λ</span> is the ⊃-intro binder and <span class="mono">λ'</span> the monadic one, so <span class="mono">bind&nbsp;t&nbsp;u</span> shows as <span class="mono">((λ'.&nbsp;u)&nbsp;t)</span>.</p>

<h2>All {len(d)} cells</h2>
<p class="h2sub">Graded by variable count, ◯-depth and ⊃-nesting, to ◯-depth 4 and ⊃-nesting 4. The last column carries the proof term for proved cells and the world counts for refuted ones.</p>
<div class="filters" id="tf">
<button aria-pressed="true" data-f="all">all</button>
<button aria-pressed="false" data-f="PROVED">proved</button>
<button aria-pressed="false" data-f="REFUTED">refuted</button>
<button aria-pressed="false" data-f="TIMEOUT">undecided</button>
<button aria-pressed="false" data-f="0v">0 variables</button>
<button aria-pressed="false" data-f="1v">1 variable</button>
<button aria-pressed="false" data-f="2v">2 variables</button>
<button aria-pressed="false" data-f="3v">3 variables</button>
</div>
<div class="tablewrap"><table><thead><tr><th>#</th><th>class</th><th>formula</th><th>verdict</th><th>time</th><th>term / model</th></tr></thead>
<tbody id="tb">{''.join(rowsH)}</tbody></table></div>

<h2>The countermodels</h2>
<p class="h2sub">All {nr} refuted cells, each refuted at its root w0 over a finite rooted poset model. {len(diff)} minimise to strictly fewer worlds than the calculus built — those carry a toggle. {len(nofm)} need no non-reflexive R<sub>m</sub> edge at all: their disproof uses only barren joins, which declare no promises, so R<sub>m</sub> stays the identity and ◯ collapses, leaving a plain intuitionistic countermodel.</p>
<div class="legend">
<span><i class="li-le"></i>≤ (Hasse)</span><span><i class="li-rm"></i>R<sub>m</sub> ⊆ ≤</span>
<span><span class="dot"></span>world</span><span><span class="dot fal"></span>fallible (⊥)</span>
<span>a cover edge carrying R<sub>m</sub> is drawn as the R<sub>m</sub> arrow only</span>
</div>
<div class="filters" id="cf">
<button aria-pressed="true" data-f="all">all</button>
<button aria-pressed="false" data-f="0v">0 variables</button>
<button aria-pressed="false" data-f="1v">1 variable</button>
<button aria-pressed="false" data-f="2v">2 variables</button>
<button aria-pressed="false" data-f="3v">3 variables</button>
</div>
<div class="grid" id="cg">{''.join(cards)}</div>

<footer>Generated from <code>batch/results.tsv</code> on branch <code>frjw-dev</code>. The <code>.lean</code> certificate beside each countermodel re-checks it by <code>decide</code>; they are kept unrun, for a single batch check.</footer>
</div>
<script id="svgs" type="application/json">{sj}</script>
<script>
var SVGS=JSON.parse(document.getElementById('svgs').textContent);
function wire(id,sel){{
  var bar=document.getElementById(id);
  bar.addEventListener('click',function(e){{
    var b=e.target.closest('button'); if(!b) return;
    [].forEach.call(bar.querySelectorAll('button'),function(x){{
      x.setAttribute('aria-pressed',x===b?'true':'false');}});
    var f=b.dataset.f;
    [].forEach.call(document.querySelectorAll(sel),function(el){{
      el.hidden = !(f==='all'||el.dataset.v===f||el.dataset.nv===f);}});
  }});
}}
wire('tf','#tb tr'); wire('cf','#cg .card');
document.addEventListener('click',function(e){{
  var b=e.target.closest('.toggle button'); if(!b) return;
  var n=b.dataset.n, rec=SVGS[n]; if(!rec) return;
  var s=rec[b.dataset.k]; if(!s) return;
  document.getElementById('pic'+n).innerHTML=s;
  [].forEach.call(b.parentNode.querySelectorAll('button'),function(x){{
    x.setAttribute('aria-pressed',x===b?'true':'false');}});
}});
</script>'''
out=sys.argv[1] if len(sys.argv)>1 else '/tmp/batch_gallery.html'
open(out,'w').write(head+body)
print(f"wrote {out}: {len(d)} cells, {nr} countermodels, {len(diff)} toggles, {len(nofm)} without Rm, {(len(head+body))//1024} KB")
