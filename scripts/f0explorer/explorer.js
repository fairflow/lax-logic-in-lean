/* F0 explorer: page code.
 *
 * Rule (METHOD-F0 §6): the page computes no mathematics.  It parses no
 * formula and evaluates no forcing.  Every name, weight, minimal form,
 * membership, order relation, cover, table result and status is read from the
 * embedded data; this code only sorts, filters, counts data rows and lays out
 * (the order diagram's coordinates come from build.py; a countermodel's ≤ is
 * drawn as the transitive reduction of its `le` table).
 */
(function () {
  'use strict';

  // ------------------------------------------------------------------ data
  const D = JSON.parse(document.getElementById('f0-data').textContent);
  const LAY = JSON.parse(document.getElementById('f0-layout').textContent);
  const META = D.meta || {};
  const FAMS = Array.isArray(D.family_defs) ? D.family_defs : [];
  const C = D.classes;
  const N = C.length;
  const posOfIndex = new Map();
  const posOfId = new Map();
  C.forEach((c, k) => { posOfIndex.set(c.index, k); posOfId.set(c.id, k); });
  const P = (i) => posOfIndex.get(i);

  const ord = Array.from({ length: N }, () => new Array(N).fill(null));
  for (const c of D.order) {
    const a = P(c.i), b = P(c.j);
    if (a !== undefined && b !== undefined) ord[a][b] = c;
  }
  const covers = D.covers.map(([i, j]) => [P(i), P(j)]).filter(([a, b]) => a !== undefined && b !== undefined);
  const coverSet = new Set(covers.map(([a, b]) => a + ',' + b));
  const below = Array.from({ length: N }, () => []);
  const above = Array.from({ length: N }, () => []);
  for (const [a, b] of covers) { above[a].push(b); below[b].push(a); }

  const OPS = {
    and: { sym: '∧', word: 'meet' },
    or: { sym: '∨', word: 'join' },
    imp: { sym: '↠', word: 'implication' },
    box: { sym: '◯', word: 'lax modality' },
  };
  const opc = {
    and: Array.from({ length: N }, () => new Array(N).fill(null)),
    or: Array.from({ length: N }, () => new Array(N).fill(null)),
    imp: Array.from({ length: N }, () => new Array(N).fill(null)),
    box: new Array(N).fill(null),
  };
  for (const c of D.ops) {
    const a = P(c.i);
    if (a === undefined || !(c.op in opc)) continue;
    if (c.op === 'box') opc.box[a] = c;
    else { const b = P(c.j); if (b !== undefined) opc[c.op][a][b] = c; }
  }
  const opCell = (op, a, b) => (op === 'box' ? opc.box[a] : opc[op][a][b]);

  function orderKind(c) {
    if (!c || c.status !== 'proved') return 'unk';
    if (c.rel === 'le') return 'le';
    if (c.rel === 'nle') return 'nle';
    return 'unk';
  }
  function opKind(c) {
    if (!c || c.status !== 'proved') return 'unk';
    if (c.result === 'notR') return 'out';
    if (posOfId.has(c.result)) return 'in';
    return 'unk';
  }

  // Named classes outside R: the optional top-level list, and the names on ∉R cells.
  const outside = new Map();
  for (const o of (D.outside_named || [])) {
    if (o && o.name != null) outside.set(String(o.name), { info: o, cells: [] });
  }
  for (const c of D.ops) {
    if (opKind(c) === 'out' && c.result_name != null) {
      const nm = String(c.result_name);
      if (!outside.has(nm)) outside.set(nm, { info: null, cells: [] });
      outside.get(nm).cells.push(c);
    }
  }

  // ------------------------------------------------------------ labels
  const esc = (s) => String(s).replace(/[&<>"']/g, (ch) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[ch]));
  // Names: `long` (in words, the primary label), `name` (the short letter name, secondary),
  // `nickname` (only for a textbook shape).  All three are read from the data.
  const name = (k) => (C[k].name == null ? null : String(C[k].name));
  const longName = (k) => (C[k].long != null ? String(C[k].long) : name(k));
  const label = (k) => longName(k) ?? 'unnamed';
  const short = (k) => name(k) ?? '·';
  const cellName = (k) => short(k).replace(/ /g, '');
  const nick = (k) => (C[k].nickname ? String(C[k].nickname) : null);
  const isCompound = (k) => C[k].name_kind === 'compound';
  const term = (k) => (C[k].term ? String(C[k].term) : null);
  const vfk = (k) => C[k].vfree_known === true;
  const minimal = (k) => (C[k].minimal != null ? C[k].minimal : C[k].formula);
  const weight = (k) => (Array.isArray(C[k].minimal_weight) && C[k].minimal_weight.length === 3 ? C[k].minimal_weight : null);
  function weightText(w) {
    return w ? `◯-depth ${w[0]} · size ${w[1]} · ◯-scope ${w[2]}` : 'weight not in the data';
  }
  // In a relation: the long name (a compound in brackets as an operand), or the minimal form of an unnamed class.
  const relName = (k) => (name(k) != null ? `<span class="cn">${esc(label(k))}</span>` : `<span class="f">${esc(minimal(k))}</span>`);
  const operand = (k) => (name(k) != null
    ? `<span class="cn">${isCompound(k) ? '(' + esc(label(k)) + ')' : esc(label(k))}</span>`
    : `(<span class="f">${esc(minimal(k))}</span>)`);
  const headOperand = (k) => (isCompound(k) ? `(${label(k)})` : label(k));

  // Lookups by name string (filters over the data, nothing derived).
  const posOfName = new Map();
  C.forEach((c, k) => { if (c.name != null) posOfName.set(String(c.name), k); });
  const FAMBY = new Map(FAMS.map((f) => [String(f.family), f]));
  const famOfLabel = new Map();
  for (const c of C.concat(D.outside_named || [])) {
    for (const f of (Array.isArray(c.families) ? c.families : [])) if (f && f.label != null) famOfLabel.set(String(f.label), String(f.family));
  }
  const OPSYM = { and: '∧', or: '∨', imp: '↠', box: '◯' };
  // The definition behind a short name: its family's definition (the index is in the name),
  // or, for a compound, the compound with its operands' family definitions.
  function defLines(nm, compound) {
    const out = [];
    const famDef = (n) => {
      const f = FAMBY.get(famOfLabel.get(n));
      return f && /=/.test(String(f.definition || '')) ? `${esc(n)}: <span class="f">${esc(f.definition)}</span>` : null;
    };
    if (compound && typeof compound === 'object') {
      // The compound name is its own definition; list its operands' family definitions.
      for (const n of [compound.x, compound.y]) { if (n != null) { const l = famDef(String(n)); if (l && !out.includes(l)) out.push(l); } }
    } else if (nm != null) {
      const l = famDef(String(nm));
      if (l) out.push(l);
    }
    return out;
  }

  function cref(k) {
    const cls = ['cref'];
    if (name(k) == null) cls.push('unnamed');
    if (vfk(k)) cls.push('vfk');
    const sub = name(k) != null && name(k) !== label(k) ? `<small>${esc(name(k))}</small>` : '';
    return `<button type="button" class="${cls.join(' ')}" data-k="c:${k}">${esc(label(k))}${sub}</button>`;
  }
  function outsideLong(nm) { const o = outside.get(nm); return o && o.info && o.info.long ? String(o.info.long) : nm; }
  function oref(nm) {
    const lg = outsideLong(nm);
    return `<button type="button" class="cref outside" data-k="x:${encodeURIComponent(nm)}">${esc(lg)}${lg !== nm ? `<small>${esc(nm)}</small>` : ''}</button>`;
  }
  const thm = (t) => `<code class="thm">${esc(t)}</code>`;

  // ------------------------------------------------------------ sorting
  const RANK = { '⊥': 0, '⊤': 1, t: 2, c: 3, g: 4, s: 5, r: 6, w: 7 };
  // Sort key of a name string: family in the naming order, then the index.
  function strKey(m) {
    if (m in RANK) return [RANK[m], 0];
    const r = /^([a-z]+)\s*(\d+)$/.exec(m);
    if (r) return [r[1] in RANK ? RANK[r[1]] : 8, Number(r[2])];
    return [8, 0];
  }
  function nameKey(k) {
    const m = name(k);
    const idx = C[k].index;
    const w = weight(k) || [0, 0, 0];
    if (m == null) return [9, 0, w[0], w[1], w[2], idx];
    if (isCompound(k)) return [8, 0, w[0], w[1], w[2], idx];
    return strKey(m).concat([0, 0, 0, idx]);
  }
  function weightKey(k) { const w = weight(k) || [0, 0, 0]; return [w[0], w[1], w[2]].concat(nameKey(k)); }
  function cmp(a, b) {
    for (let i = 0; i < Math.max(a.length, b.length); i++) {
      const x = a[i] ?? 0, y = b[i] ?? 0;
      if (x < y) return -1;
      if (x > y) return 1;
    }
    return 0;
  }
  function axis() {
    const key = state.sort === 'weight' ? weightKey : nameKey;
    return Array.from({ length: N }, (_, k) => k).sort((a, b) => cmp(key(a), key(b)));
  }

  // ------------------------------------------------------------ state
  const store = {
    get(k, d) { try { const v = localStorage.getItem('f0x.' + k); return v === null ? d : v; } catch (e) { return d; } },
    set(k, v) { try { localStorage.setItem('f0x.' + k, v); } catch (e) { /* storage unavailable */ } },
  };
  const state = {
    view: ['order', 'pairs', 'tables', 'classes'].includes(store.get('view', 'order')) ? store.get('view', 'order') : 'order',
    op: ['and', 'or', 'imp'].includes(store.get('op', 'and')) ? store.get('op', 'and') : 'and',
    sort: store.get('sort', 'name') === 'weight' ? 'weight' : 'name',
    vf: store.get('vf', '0') === '1',
    theme: store.get('theme', 'auto'),
    panel: null,
    back: [],
    row: null,
  };

  const $ = (id) => document.getElementById(id);
  const view = $('view');
  const panelBody = $('panel-body');
  const panelKind = $('panel-kind');
  const tip = $('tip');

  // ------------------------------------------------------------ tallies (counts of data rows)
  function orderTally() {
    const t = { le: 0, nle: 0, unk: 0 };
    for (let a = 0; a < N; a++) for (let b = 0; b < N; b++) if (a !== b) t[orderKind(ord[a][b])]++;
    return t;
  }
  function stampText() {
    const checked = Array.isArray(META.checked) ? META.checked.join(', ') : 'not stated';
    return `Data generated ${esc(D.generated)} · commit ${esc(D.commit)} · kernel-checked parts: ${esc(checked)} · pins ${esc(META.pins || 'not stated')}`;
  }
  function sortControl() {
    return `<label class="small">Sort <select data-sort>
      <option value="name"${state.sort === 'name' ? ' selected' : ''}>by name</option>
      <option value="weight"${state.sort === 'weight' ? ' selected' : ''}>by weight</option></select></label>`;
  }

  // ------------------------------------------------------------ about (three paragraphs)
  function famSym(f) { return f === 'bot' ? '⊥' : f === 'top' ? '⊤' : String(f); }
  function renderAbout() {
    const defs = FAMS.filter((f) => /=/.test(String(f.definition || ''))).map((f) =>
      `${f.word && f.word !== famSym(f.family) ? `<em>${esc(f.word)}</em> ` : ''}<span class="f">${esc(f.definition)}</span>${f.lean ? ` (<code>${esc(f.lean)}</code>)` : ''}`).join('; ');
    const order = FAMS.map((f) => esc(famSym(f.family))).join(', ');
    const domain = FAMS.filter((f) => Array.isArray(f.indices) && f.family !== 'bot' && f.family !== 'top' && f.indices.length)
      .map((f) => `${esc(f.family)}${esc(Math.min(...f.indices))}…${esc(f.family)}${esc(Math.max(...f.indices))}`).join(', ');
    $('about-body').innerHTML =
      `<p>F0 is the variable-free fragment of propositional lax logic (PLL). The page shows the frontier, the classes
      of F0 whose pairwise order is all certified, ordered by derivability (u below v when [u] ⊢ v), with the tables
      of ∧, ∨, ↠ and ◯. Hover over a class for its definition, minimal form and weight (◯-depth, size, ◯-scope);
      click a class, edge, pair or cell for its Lean theorems and, for ⊬, the countermodel.</p>
      <p>The RN embedding substitutes ◯⊥ for p in the Rieger–Nishimura formulas rn n of one-variable intuitionistic
      logic. The families: ${defs}. A class takes its first certified family name (order ${order}, then the smallest
      index; searched over ${domain}), else a compound name x ∘ y over named classes, certified by two bridge facts.
      Textbook shapes also carry a nickname.</p>
      <p>Beyond the frontier: certified distinct from every class of the frontier (it may still have a family name).
      Unknown: not yet decided. Every fact shown is a Lean theorem pinned at ${esc(META.pins || '(pins not stated)')}.
      Results on the whole of F0 (the elements not above t3, filters, the completion F*) are in Paper III,
      <em>The Order of F0</em>.</p>`;
  }

  // ------------------------------------------------------------ views
  function render() {
    document.querySelectorAll('.tabs button').forEach((b) => b.setAttribute('aria-selected', String(b.dataset.view === state.view)));
    if (state.view === 'order') view.innerHTML = renderOrder();
    else if (state.view === 'pairs') view.innerHTML = renderPairs();
    else if (state.view === 'tables') view.innerHTML = renderTables();
    else view.innerHTML = renderClasses();
    applySel();
  }

  function shelf() {
    let h = '<div class="shelf"><h3>Beyond the frontier</h3>';
    const names = [...outside.keys()].sort((a, b) => cmp(strKey(a), strKey(b)) || (a < b ? -1 : a > b ? 1 : 0));
    if (outside.size) h += `<div class="chips">${names.map(oref).join('')}</div>`;
    else h += '<p class="small muted">None named in this data.</p>';
    const b = D.boundary || {};
    let outCells = 0, unnamedOut = 0;
    for (const c of D.ops) if (opKind(c) === 'out') { outCells++; if (c.result_name == null) unnamedOut++; }
    h += `<p class="small muted">Table cells beyond the frontier: ${esc(b.notR ?? outCells)}, ${unnamedOut} of them unnamed;
      unknown: ${esc(b.unknown ?? 0)}.</p></div>`;
    return h;
  }

  function renderOrder() {
    const t = orderTally();
    let h = `<div class="view-head"><h2>The frontier</h2></div>`;
    if (!covers.length) {
      h += '<p class="empty">No covers in the data (the order is not fully certified), so no diagram is drawn.</p>';
    } else {
      const W = LAY.width, H = LAY.height;
      let s = `<div class="diagram-wrap"><svg class="diagram" viewBox="0 0 ${W} ${H}" role="group" aria-label="Hasse diagram of the frontier">`;
      s += `<rect class="frame" x="3" y="3" width="${W - 6}" height="${H - 6}" rx="10"></rect>`;
      s += `<text class="frame-label" x="14" y="21">${N} classes · ${esc(D.generated)}</text>`;
      const hh = (p) => (p.h || 24) / 2;
      for (const [a, b] of covers) {
        const p = LAY.nodes[a], q = LAY.nodes[b];
        const key = `e:${a},${b}`;
        const qBottom = q.y + hh(q) + (q.sub ? 13 : 0);
        s += `<g class="edge" data-k="${key}" role="button" aria-label="${esc(label(a))} ⋖ ${esc(label(b))}"><line class="hit" x1="${p.x}" y1="${p.y}" x2="${q.x}" y2="${q.y}"></line>` +
          `<line class="vis" x1="${p.x}" y1="${p.y - hh(p)}" x2="${q.x}" y2="${qBottom}"></line></g>`;
      }
      for (let k = 0; k < N; k++) {
        const p = LAY.nodes[k];
        const h2 = hh(p);
        const lines = Array.isArray(p.lines) && p.lines.length ? p.lines : [label(k)];
        const cls = ['node'];
        if (name(k) == null) cls.push('unnamed');
        if (vfk(k)) cls.push('vfk');
        s += `<g class="${cls.join(' ')}" data-k="c:${k}" tabindex="0" role="button" aria-label="${esc(label(k))}${name(k) != null && name(k) !== label(k) ? ' (' + esc(name(k)) + ')' : ''}" transform="translate(${p.x},${p.y})">` +
          `<rect class="vfring" x="${-p.w / 2 - 3.5}" y="${-h2 - 3.5}" width="${p.w + 7}" height="${2 * h2 + 7}" rx="${Math.min(15.5, h2 + 3.5)}"></rect>` +
          `<rect class="body" x="${-p.w / 2}" y="${-h2}" width="${p.w}" height="${2 * h2}" rx="${Math.min(12, h2)}"></rect>` +
          lines.map((t, i) => `<text x="0" y="${((i - (lines.length - 1) / 2) * 14 + 0.5).toFixed(1)}">${esc(t)}</text>`).join('') +
          (p.sub ? `<text class="sub" x="0" y="${(h2 + 8.5).toFixed(1)}">${esc(p.sub)}</text>` : '') + '</g>';
      }
      s += '</svg></div>';
      h += s;
    }
    h += `<p class="tally">${t.le} [u] ⊢ v · ${t.nle} [u] ⊬ v · ${t.unk} unknown · ${covers.length} covers u ⋖ v (no class of the
      frontier strictly between). Click a node or an edge for its certificates.</p>`;
    h += shelf();
    return h;
  }

  // Grid headers carry both names: the long name (vertical in column heads) on wide
  // screens, the short name on compact screens (CSS chooses).
  function gridHead(ax, corner) {
    let h = `<colgroup><col class="hcol" style="width:${headColWidth()}"></colgroup>`;
    h += `<thead><tr><th class="corner" scope="col">${corner}</th>`;
    for (const k of ax) {
      h += `<th scope="col" class="${name(k) == null ? 'unnamed' : ''} ${vfk(k) ? 'vfk' : ''}" data-k="c:${k}">` +
        `<span class="vt">${esc(label(k))}</span><span class="st">${esc(cellName(k))}</span></th>`;
    }
    return h + '</tr></thead>';
  }
  function headColWidth() { return window.matchMedia('(max-width: 600px)').matches ? '30px' : '150px'; }
  function rowHead(k) {
    return `<th scope="row" class="${name(k) == null ? 'unnamed' : ''} ${vfk(k) ? 'vfk' : ''}" data-k="c:${k}">` +
      `<span class="lt">${esc(label(k))}</span><span class="st">${esc(cellName(k))}</span></th>`;
  }

  function rowSelect(ax) {
    if (state.row == null || !ax.includes(state.row)) state.row = ax[0];
    return `<label class="small">Row <select data-row>${ax.map((k) =>
      `<option value="${k}"${k === state.row ? ' selected' : ''}>${esc(label(k))}${name(k) == null ? ': ' + esc(minimal(k)) : ''}</option>`).join('')}</select></label>`;
  }

  function renderPairs() {
    const ax = axis();
    let h = `<div class="view-head"><h2>Pairs: [row] ⊢ column?</h2>${sortControl()}</div>`;
    h += `<div class="grid-wrap"><table class="grid">${gridHead(ax, '⊢?')}<tbody>`;
    for (const a of ax) {
      h += `<tr>${rowHead(a)}`;
      for (const b of ax) {
        if (a === b) { h += '<td class="diag"></td>'; continue; }
        const kind = orderKind(ord[a][b]);
        const cls = ['k-' + kind];
        if (coverSet.has(a + ',' + b)) cls.push('k-cov');
        h += `<td class="${cls.join(' ')}" data-k="p:${a},${b}">${kind === 'le' ? '⊢' : kind === 'nle' ? '⊬' : '?'}</td>`;
      }
      h += '</tr>';
    }
    h += '</tbody></table></div>';
    h += `<div class="legend"><span><i class="sw le"></i>⊢</span><span><i class="sw nle"></i>⊬ (countermodel)</span>
      <span><i class="sw unk"></i>unknown</span><span><i class="sw cov"></i>cover</span></div>`;
    h += `<div class="rowlist">${rowSelect(ax)}<ul>${ax.filter((b) => b !== state.row).map((b) => {
      const kind = orderKind(ord[state.row][b]);
      const rel = kind === 'le' ? '⊢' : kind === 'nle' ? '⊬' : '? (unknown)';
      return `<li data-k="p:${state.row},${b}"><i class="sw ${kind}"></i><span>[${relName(state.row)}] ${rel} ${relName(b)}</span></li>`;
    }).join('')}</ul></div>`;
    return h;
  }

  function opCellHtml(op, a, b) {
    const c = opCell(op, a, b);
    const kind = opKind(c);
    const key = `o:${op}:${a}:${op === 'box' ? '' : b}`;
    if (kind === 'in') {
      const r = posOfId.get(c.result);
      const cls = ['k-in'];
      if (vfk(r)) cls.push('vfk');
      if (name(r) == null) cls.push('unnamed-res');
      return `<td class="${cls.join(' ')}" data-k="${key}">${esc(cellName(r))}</td>`;
    }
    if (kind === 'out') {
      const nm = c.result_name;
      return `<td class="k-out${nm != null ? ' named' : ''}" data-k="${key}">${nm != null ? esc(nm) : ''}</td>`;
    }
    return `<td class="k-unk" data-k="${key}">?</td>`;
  }

  function bars() {
    const per = (D.boundary && D.boundary.per_op) || {};
    let h = '<div class="bars">';
    for (const op of ['and', 'or', 'imp', 'box']) {
      const p = per[op];
      if (!p) continue;
      const tot = p.cells || 1;
      const pc = (x) => (100 * (x || 0) / tot).toFixed(2) + '%';
      h += `<div class="bar-row"><span class="op">${OPS[op].sym}</span>
        <span class="bar" aria-hidden="true"><i class="b-in" style="width:${pc(p.inR)}"></i><i class="b-out" style="width:${pc(p.notR)}"></i><i class="b-unk" style="width:${pc(p.unknown)}"></i></span>
        <span class="nums">${esc(p.inR)} in · ${esc(p.notR)} beyond · ${esc(p.unknown)} unknown</span></div>`;
    }
    return h + '</div>';
  }

  function renderTables() {
    const ax = axis();
    const op = state.op;
    const sym = OPS[op].sym;
    let h = `<div class="view-head"><h2>Tables</h2><span class="seg" role="group" aria-label="Operation">${['and', 'or', 'imp'].map((o) =>
      `<button type="button" data-op="${o}" aria-pressed="${o === op}">${OPS[o].sym}</button>`).join('')}</span>${sortControl()}</div>`;
    h += bars();
    h += `<div class="grid-wrap"><table class="grid">${gridHead(ax, 'row ' + sym + ' col; ◯ col')}<tbody class="box-row"><tr><th scope="row" class="corner">◯ col</th>`;
    for (const b of ax) h += opCellHtml('box', b, null);
    h += '</tr></tbody><tbody>';
    for (const a of ax) {
      h += `<tr>${rowHead(a)}`;
      for (const b of ax) h += opCellHtml(op, a, b);
      h += '</tr>';
    }
    h += '</tbody></table></div>';
    h += `<div class="legend"><span><i class="sw in"></i>in the frontier</span>
      <span><i class="sw out"></i>beyond it (named in italics)</span><span><i class="sw unk"></i>unknown</span>
      <span><i class="sw vf"></i>known ∨-free member (switch on)</span></div>`;
    const list = (o, a, b) => {
      const c = opCell(o, a, b);
      const kind = opKind(c);
      const expr = o === 'box' ? `◯ ${operand(a)}` : `${operand(a)} ${OPS[o].sym} ${operand(b)}`;
      let res;
      if (kind === 'in') res = relName(posOfId.get(c.result));
      else if (kind === 'out') res = c.result_name != null ? `${esc(c.result_name)}, beyond the frontier` : 'beyond the frontier';
      else res = 'unknown';
      return `<li data-k="o:${o}:${a}:${o === 'box' ? '' : b}"><i class="sw ${kind}"></i><span>${expr} = ${res}</span></li>`;
    };
    h += `<div class="rowlist">${rowSelect(ax)}<ul>${list('box', state.row, null)}${ax.map((b) => list(op, state.row, b)).join('')}</ul></div>`;
    return h;
  }

  function renderClasses() {
    const ax = axis();
    let h = `<div class="view-head"><h2>Classes</h2>${sortControl()}</div><div class="cards">`;
    for (const k of ax) {
      const c = C[k];
      const sn = name(k) != null && name(k) !== label(k) ? `<span class="sn f">${esc(name(k))}</span>` : '';
      h += `<button type="button" class="card${vfk(k) ? ' vfk' : ''}" data-k="c:${k}">
        <div><span class="nm${name(k) == null ? ' unnamed' : ''}">${esc(label(k))}</span>${sn}${term(k) ? `<code class="term">${esc(term(k))}</code>` : ''}</div>
        ${nick(k) ? `<div class="nick">“${esc(nick(k))}”</div>` : ''}
        <div class="min f">${esc(minimal(k))}</div>
        <div class="meta">${weightText(weight(k))} · ${esc(c.members_known ?? '?')} known members</div>
        <div class="meta">∨-free: ${c.vfree_known ? `<span class="f">${esc(c.vfree_witness)}</span>` : 'none known'}</div></button>`;
    }
    h += '</div>';
    h += shelf();
    return h;
  }

  // ------------------------------------------------------------ countermodel drawing
  function cmSvg(m, fromK, toK) {
    const n = m.n | 0;
    const le = (i, j) => !!(m.le && m.le[i] && m.le[i][j]);
    const S = (i) => !!(m.S && m.S[i]);
    // ≤ drawn up to transitivity: the transitive reduction of the given table.
    const edges = [];
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
      if (i === j || !le(i, j)) continue;
      let mid = false;
      for (let k = 0; k < n && !mid; k++) if (k !== i && k !== j && le(i, k) && le(k, j)) mid = true;
      if (!mid) edges.push([i, j]);
    }
    const layer = new Array(n).fill(0);
    for (let it = 0; it < n; it++) for (const [i, j] of edges) if (layer[j] < layer[i] + 1) layer[j] = layer[i] + 1;
    const top = Math.max(0, ...layer);
    const rows = Array.from({ length: top + 1 }, () => []);
    for (let i = 0; i < n; i++) rows[layer[i]].push(i);
    const DX = 52, DY = 50, R = 10;
    const width = Math.max(...rows.map((r) => r.length)) * DX + 110;
    const height = top * DY + 2 * R + 34;
    const pos = new Array(n);
    rows.forEach((r, L) => r.forEach((w, idx) => {
      pos[w] = { x: 40 + (idx - (r.length - 1) / 2) * DX + (Math.max(...rows.map((q) => q.length)) - 1) * DX / 2, y: height - 20 - L * DY };
    }));
    let s = `<svg class="cm" viewBox="0 0 ${width} ${height}" width="${width}" height="${height}" role="img" aria-label="Countermodel with ${n} worlds">`;
    for (const [i, j] of edges) s += `<line x1="${pos[i].x}" y1="${pos[i].y - R}" x2="${pos[j].x}" y2="${pos[j].y + R}"></line>`;
    for (let i = 0; i < n; i++) {
      if (i === m.root) s += `<circle class="root-ring" cx="${pos[i].x}" cy="${pos[i].y}" r="${R + 4}"></circle>`;
      s += `<circle class="w${S(i) ? ' s' : ''}" cx="${pos[i].x}" cy="${pos[i].y}" r="${R}"></circle>`;
      s += `<text class="wl" x="${pos[i].x}" y="${pos[i].y + 0.5}">${i}</text>`;
      if (S(i)) s += `<text class="sl" x="${pos[i].x - R - 14}" y="${pos[i].y - R + 1}">S</text>`;
      if (i === m.root) s += `<text x="${pos[i].x + R + 8}" y="${pos[i].y + 4}">root</text>`;
    }
    s += '</svg>';
    return s + `<p class="note">The root refutes ${relName(fromK)} ↠ ${relName(toK)}.
      <i class="sw spt"></i> S: the S-points; ≤ up to transitivity.</p>`;
  }

  // ------------------------------------------------------------ panels
  function factBlock(a, b) {
    const c = ord[a][b];
    const kind = orderKind(c);
    if (kind === 'le') {
      const nodes = c.cert && c.cert.nodes != null ? `closed tableau, ${esc(c.cert.nodes)} nodes` : 'closed tableau';
      return `<div class="fact le"><div class="rel">[${relName(a)}] ⊢ ${relName(b)}</div><div>${thm(c.theorem)}</div>
        <div class="note">${nodes} · status ${esc(c.status)}</div></div>`;
    }
    if (kind === 'nle') {
      const m = c.cert || {};
      return `<div class="fact nle"><div class="rel">[${relName(a)}] ⊬ ${relName(b)}</div><div>${thm(c.theorem)}</div>
        <div class="note">countermodel, ${esc(m.n)} world${m.n === 1 ? '' : 's'} · status ${esc(c.status)}</div>${m.le ? cmSvg(m, a, b) : ''}</div>`;
    }
    return `<div class="fact unk"><div class="rel">[${relName(a)}] ? ${relName(b)}</div>
      <div class="note">unknown: not yet decided${c ? ` (status ${esc(c.status)}; theorem ${thm(c.theorem)})` : ' (no cell in the data)'}</div></div>`;
  }

  function famItem(f) {
    if (f == null) return '';
    if (typeof f !== 'object') return `<li><span class="f">${esc(f)}</span></li>`;
    const fam = f.family === 'bot' ? '⊥' : f.family === 'top' ? '⊤' : null;
    const nm = f.label != null ? f.label : f.name != null ? f.name : fam != null ? fam : `${f.family ?? '?'}${f.index ?? ''}`;
    const bridge = Array.isArray(f.bridge) && f.bridge.length ? `<div class="note">bridge: ${f.bridge.map(thm).join(', ')}</div>` : '';
    return `<li><span class="f">${esc(nm)}</span>${f.term ? ` ${thm(f.term)}` : ''}${bridge}</li>`;
  }

  function classPanel(k) {
    const c = C[k];
    const legacyText = `legacy label ${esc(c.legacy ?? c.id)}${c.legacy_const ? ` (${esc(c.legacy_const)})` : ''}`;
    let h = `<h2${name(k) == null ? ' class="muted"' : ''}>${esc(label(k))}</h2>`;
    // An unnamed class has no short handle but its legacy label: shown at the top, still styled as legacy.
    if (name(k) == null) h += `<p class="legacy legacy-top">${legacyText}</p>`;
    if (name(k) != null) {
      h += `<p class="names">${name(k) !== label(k) ? `<span class="sn f">${esc(name(k))}</span> ` : ''}${term(k) ? thm(term(k)) : ''}</p>`;
    }
    if (nick(k)) h += `<p class="nick">“${esc(nick(k))}”</p>`;
    const defs = defLines(name(k), isCompound(k) ? c.compound : null);
    if (defs.length) h += `<div class="defs">${defs.map((l) => `<div>${l}</div>`).join('')}</div>`;
    h += `<h3>Minimal form</h3><p class="f">${esc(minimal(k))}</p><p class="note">${weightText(weight(k))}</p>`;
    if (Array.isArray(c.minimal_theorems) && c.minimal_theorems.length) h += `<p class="note">member by ${c.minimal_theorems.map(thm).join(', ')}</p>`;
    if (isCompound(k)) {
      // A compound name, shown the way a family membership is: the name, its term, its bridge facts.
      const comp = c.compound || {};
      const ops = [comp.x, comp.y].filter((n) => n != null).map((n) => (posOfName.has(String(n)) ? cref(posOfName.get(String(n))) : esc(n))).join(' ');
      const bridge = Array.isArray(c.name_bridge) && c.name_bridge.length ? `<div class="note">bridge: ${c.name_bridge.map(thm).join(', ')}</div>` : '';
      h += `<h3>Compound name</h3><ul><li><span class="f">${esc(name(k))}</span>${term(k) ? ` ${thm(term(k))}` : ''}${bridge}` +
        `${ops ? `<div class="note">operands: ${ops}</div>` : ''}</li></ul>`;
    }
    const fams = Array.isArray(c.families) ? c.families : [];
    h += `<h3>Family memberships</h3>${fams.length ? `<ul>${fams.map(famItem).join('')}</ul>` : '<p class="empty">none in the data</p>'}`;
    h += '<h3>∨-free member</h3>';
    if (c.vfree_known) {
      h += `<p class="f">${esc(c.vfree_witness)}</p>`;
      if (Array.isArray(c.vfree_theorems) && c.vfree_theorems.length) h += `<p class="note">member by ${c.vfree_theorems.map(thm).join(', ')}</p>`;
    } else h += '<p class="empty">none known</p>';
    const cov = (list, dir) => (list.length ? list.slice().sort((x, y) => cmp(nameKey(x), nameKey(y))).map((m) =>
      `<span>${cref(m)} <button type="button" class="lnk" data-k="e:${dir === 'below' ? m + ',' + k : k + ',' + m}" title="open the cover">⋖</button></span>`).join(' ')
      : '<span class="empty">none</span>');
    h += `<h3>Covers in the frontier</h3><p>below: ${cov(below[k], 'below')}</p><p>above: ${cov(above[k], 'above')}</p>`;
    h += `<h3>Compare with</h3><select data-compare="${k}"><option value="">choose a class…</option>${axis().filter((m) => m !== k).map((m) =>
      `<option value="${m}">${esc(label(m))}${name(m) == null ? ': ' + esc(minimal(m)) : ''}</option>`).join('')}</select>`;
    const members = [c.formula].concat(Array.isArray(c.members) ? c.members.filter((f) => f !== c.formula) : []);
    h += `<h3>Known members</h3><p>${esc(c.members_known ?? members.length)} known · status ${esc(c.members_status ?? 'not stated')}</p>`;
    h += `<details><summary>show the list</summary><ul>${members.map((f) => `<li class="f">${esc(f)}</li>`).join('')}</ul></details>`;
    if (name(k) != null) h += `<p class="legacy">${legacyText}</p>`;
    return h;
  }

  function pairPanel(a, b, asCover) {
    let h = asCover
      ? `<h2>${esc(headOperand(a))} ⋖ ${esc(headOperand(b))}</h2><p class="note">A cover: no class of the frontier strictly between.</p>`
      : `<h2>${esc(headOperand(a))} · ${esc(headOperand(b))}</h2>`;
    h += `<p>${cref(a)} ${cref(b)}</p>`;
    h += factBlock(a, b) + factBlock(b, a);
    return h;
  }

  function opPanel(op, a, b) {
    const c = opCell(op, a, b);
    const kind = opKind(c);
    const sym = OPS[op].sym;
    const headExpr = op === 'box' ? `◯ ${esc(headOperand(a))}` : `${esc(headOperand(a))} ${sym} ${esc(headOperand(b))}`;
    const X = op === 'box' ? `◯ ${operand(a)}` : `${operand(a)} ${sym} ${operand(b)}`;
    let h = `<h2>${headExpr}</h2><p>${cref(a)}${op === 'box' ? '' : ' ' + cref(b)}</p>`;
    if (!c) return h + '<p class="empty">No cell in the data.</p>';
    h += `<h3>Formula</h3><p class="f">${esc(c.formula)}</p><h3>Result</h3>`;
    const th = Array.isArray(c.theorems) ? c.theorems : [];
    if (kind === 'in') {
      const r = posOfId.get(c.result);
      h += `<p>⊣⊢ ${cref(r)} <span class="note">${esc(minimal(r))}</span></p>`;
      h += `<div class="fact le"><div class="rel">[${X}] ⊢ ${relName(r)}</div><div>${th[0] ? thm(th[0]) : '<span class="empty">no theorem in the data</span>'}</div></div>`;
      h += `<div class="fact le"><div class="rel">[${relName(r)}] ⊢ ${X}</div><div>${th[1] ? thm(th[1]) : '<span class="empty">no theorem in the data</span>'}</div></div>`;
      h += `<p class="note">status ${esc(c.status)}</p>`;
    } else if (kind === 'out') {
      const seps = Array.isArray(c.separations) ? c.separations : [];
      const ks = new Set(seps.map((s) => P(s.k)).filter((x) => x !== undefined));
      h += `<p><strong class="out-badge">beyond the frontier</strong>${c.result_name != null ? ` · named ${oref(String(c.result_name))}` : ' · no name in the data'}</p>`;
      if (c.result_name != null && Array.isArray(c.result_name_bridge) && c.result_name_bridge.length) {
        h += `<p class="note">${X} ⊣⊢ <span class="cn">${esc(outsideLong(String(c.result_name)))}</span> by ${c.result_name_bridge.map(thm).join(', ')}</p>`;
      }
      h += `<p>${seps.length} certified separations${ks.size === N ? ', one from each class of the frontier' : ''}.</p>`;
      h += `<details><summary>show the separations</summary><p class="note">X = ${X}</p><ul>${seps.map((s) => {
        const k = P(s.k);
        const nk = k === undefined ? esc(s.k) : relName(k);
        const rel = s.dir === 'bwd' ? `[${nk}] ⊬ X` : `[X] ⊬ ${nk}`;
        return `<li><span class="f">${rel}</span><br>${thm(s.theorem)} <span class="note">${s.worlds != null ? esc(s.worlds) + (s.worlds === 1 ? ' world' : ' worlds') : ''}</span></li>`;
      }).join('')}</ul></details>`;
    } else {
      h += `<p class="empty">unknown: not yet decided (status ${esc(c.status)})</p>`;
    }
    return h;
  }

  function outsidePanel(nm) {
    const o = outside.get(nm);
    const lg = outsideLong(nm);
    let h = `<h2>${esc(lg)}</h2><p><strong class="out-badge">beyond the frontier</strong></p>`;
    if (!o) return h + '<p class="empty">Not in the data.</p>';
    const info = o.info;
    h += `<p class="names">${lg !== nm ? `<span class="sn f">${esc(nm)}</span> ` : ''}${info && info.term ? thm(info.term) : ''}</p>`;
    if (info && info.nickname) h += `<p class="nick">“${esc(info.nickname)}”</p>`;
    const defs = defLines(nm, null);
    if (defs.length) h += `<div class="defs">${defs.map((l) => `<div>${l}</div>`).join('')}</div>`;
    if (info) {
      if (info.minimal) h += `<h3>Minimal form</h3><p class="f">${esc(info.minimal)}</p><p class="note">${weightText(Array.isArray(info.minimal_weight) ? info.minimal_weight : null)}</p>`;
      if (Array.isArray(info.minimal_theorems) && info.minimal_theorems.length) h += `<p class="note">member by ${info.minimal_theorems.map(thm).join(', ')}</p>`;
      if (Array.isArray(info.families) && info.families.length) h += `<h3>Family memberships</h3><ul>${info.families.map(famItem).join('')}</ul>`;
      h += '<h3>Separation from the frontier</h3>';
      if (info.separations != null) h += `<p>${esc(info.separations)} certified separations.</p>`;
      if (Array.isArray(info.theorems) && info.theorems.length) h += `<details><summary>show the theorems</summary><ul>${info.theorems.map((t) => `<li>${thm(t)}</li>`).join('')}</ul></details>`;
    } else {
      h += '<p class="note">No further entry in the data.</p>';
    }
    h += `<h3>Table cells with this result</h3>`;
    if (o.cells.length) {
      h += `<ul>${o.cells.map((c) => {
        const a = P(c.i), b = c.j == null ? null : P(c.j);
        const expr = c.op === 'box' ? `◯ ${operand(a)}` : `${operand(a)} ${OPS[c.op].sym} ${operand(b)}`;
        return `<li><button type="button" class="lnk" data-k="o:${c.op}:${a}:${c.op === 'box' ? '' : b}">${expr}</button></li>`;
      }).join('')}</ul>`;
    } else h += '<p class="empty">none</p>';
    return h;
  }

  function hintPanel() {
    return `<p class="muted">Select a class, edge, pair or cell for its certificates.</p>`;
  }

  function parseKey(key) {
    if (!key) return null;
    const i = key.indexOf(':');
    const t = key.slice(0, i), v = key.slice(i + 1);
    if (t === 'c') return { t, k: Number(v) };
    if (t === 'p' || t === 'e') { const [a, b] = v.split(',').map(Number); return { t, a, b }; }
    if (t === 'o') { const [op, a, b] = v.split(':'); return { t, op, a: Number(a), b: b === '' ? null : Number(b) }; }
    if (t === 'x') return { t, nm: decodeURIComponent(v) };
    return null;
  }

  function renderPanel() {
    const p = parseKey(state.panel);
    let kind = 'Details', h = hintPanel();
    if (p) {
      if (p.t === 'c' && C[p.k]) { kind = 'Class'; h = classPanel(p.k); }
      else if (p.t === 'p' && C[p.a] && C[p.b]) { kind = 'Pair'; h = pairPanel(p.a, p.b, false); }
      else if (p.t === 'e' && C[p.a] && C[p.b]) { kind = 'Cover'; h = pairPanel(p.a, p.b, true); }
      else if (p.t === 'o' && p.op in OPS && C[p.a]) { kind = 'Table cell'; h = opPanel(p.op, p.a, p.b); }
      else if (p.t === 'x') { kind = 'Beyond the frontier'; h = outsidePanel(p.nm); }
    }
    panelKind.textContent = kind;
    panelBody.innerHTML = h;
    panelBody.scrollTop = 0;
    $('back-btn').disabled = state.back.length === 0;
    applySel();
  }

  function applySel() {
    document.querySelectorAll('.sel, .near').forEach((e) => e.classList.remove('sel', 'near'));
    if (!state.panel) return;
    view.querySelectorAll(`[data-k="${CSS.escape(state.panel)}"]`).forEach((e) => e.classList.add('sel'));
    const p = parseKey(state.panel);
    if (p && p.t === 'c') {
      for (const m of below[p.k]) view.querySelectorAll(`[data-k="e:${m},${p.k}"]`).forEach((e) => e.classList.add('near'));
      for (const m of above[p.k]) view.querySelectorAll(`[data-k="e:${p.k},${m}"]`).forEach((e) => e.classList.add('near'));
    }
  }

  function open(key, push = true) {
    if (push && state.panel && state.panel !== key) state.back.push(state.panel);
    state.panel = key;
    renderPanel();
    hideTip();
    const panel = $('panel');
    const r = panel.getBoundingClientRect();
    if (window.matchMedia('(max-width: 1199px)').matches && (r.top > window.innerHeight * 0.6 || r.bottom < 0)) {
      panel.scrollIntoView({ behavior: 'smooth', block: 'start' });
    }
  }

  // ------------------------------------------------------------ tooltip (mouse and keyboard focus)
  function tipHtml(key) {
    const p = parseKey(key);
    if (!p) return null;
    const cls = (k) => `<div class="tn">${esc(label(k))}</div>` +
      (name(k) != null ? `<div class="ts">${name(k) !== label(k) ? `<span class="f">${esc(name(k))}</span> · ` : ''}${term(k) ? `<code>${esc(term(k))}</code>` : ''}</div>` : '') +
      (nick(k) ? `<div class="tk">“${esc(nick(k))}”</div>` : '') +
      defLines(name(k), isCompound(k) ? C[k].compound : null).map((l) => `<div class="td">${l}</div>`).join('') +
      `<div class="tf">${esc(minimal(k))}</div><div class="tw">${weightText(weight(k))}${vfk(k) ? ' · known ∨-free member' : ''}</div>`;
    if (p.t === 'c' && C[p.k]) return cls(p.k);
    if ((p.t === 'p' || p.t === 'e') && C[p.a] && C[p.b]) {
      if (p.t === 'e') return `<div class="tn">${esc(headOperand(p.a))} ⋖ ${esc(headOperand(p.b))}</div><div class="tw">a cover; click for its certificates</div>`;
      const kind = orderKind(ord[p.a][p.b]);
      const rel = kind === 'le' ? '⊢' : kind === 'nle' ? '⊬' : '? (unknown)';
      return `<div class="tf">[${relName(p.a)}] ${rel} ${relName(p.b)}</div><div class="tw">${ord[p.a][p.b] ? esc(ord[p.a][p.b].theorem) : ''}</div>`;
    }
    if (p.t === 'o' && p.op in OPS && C[p.a]) {
      const c = opCell(p.op, p.a, p.b);
      const kind = opKind(c);
      const expr = p.op === 'box' ? `◯ ${operand(p.a)}` : `${operand(p.a)} ${OPS[p.op].sym} ${operand(p.b)}`;
      let res = 'unknown';
      if (kind === 'in') { const r = posOfId.get(c.result); return `<div class="tf">${expr} =</div>${cls(r)}`; }
      if (kind === 'out') res = c.result_name != null ? `${esc(c.result_name)}, beyond the frontier` : 'beyond the frontier';
      return `<div class="tf">${expr} = ${res}</div>`;
    }
    if (p.t === 'x') {
      const o = outside.get(p.nm);
      const info = o && o.info;
      const lg = outsideLong(p.nm);
      return `<div class="tn">${esc(lg)} <span class="tw">beyond the frontier</span></div>` +
        `<div class="ts">${lg !== p.nm ? `<span class="f">${esc(p.nm)}</span> · ` : ''}${info && info.term ? `<code>${esc(info.term)}</code>` : ''}</div>` +
        (info && info.nickname ? `<div class="tk">“${esc(info.nickname)}”</div>` : '') +
        defLines(p.nm, null).map((l) => `<div class="td">${l}</div>`).join('') +
        (info && info.minimal ? `<div class="tf">${esc(info.minimal)}</div><div class="tw">${weightText(info.minimal_weight)}</div>` : '');
    }
    return null;
  }
  let tipShown = null;
  function showTip(html, x, y) {
    if (html !== tipShown) { tip.innerHTML = html; tipShown = html; }
    tip.hidden = false;
    const r = tip.getBoundingClientRect();
    let left = x + 14, top = y + 16;
    if (left + r.width > window.innerWidth - 8) left = Math.max(8, x - r.width - 14);
    if (top + r.height > window.innerHeight - 8) top = Math.max(8, y - r.height - 12);
    tip.style.left = left + 'px';
    tip.style.top = top + 'px';
  }
  function hideTip() { tip.hidden = true; }
  let tipKey = null, tipCur = null;
  document.addEventListener('pointermove', (e) => {
    if (e.pointerType !== 'mouse') return;
    const t = e.target.closest && e.target.closest('[data-k]');
    if (!t || t.closest('#panel')) { if (tipKey) { tipKey = null; tipCur = null; hideTip(); } return; }
    const key = t.getAttribute('data-k');
    if (key !== tipKey) { tipKey = key; tipCur = tipHtml(key); }
    if (!tipCur) { hideTip(); return; }
    showTip(tipCur, e.clientX, e.clientY);
  });
  document.addEventListener('pointerleave', () => { tipKey = null; tipCur = null; hideTip(); });
  document.addEventListener('scroll', () => { tipKey = null; tipCur = null; hideTip(); }, true);
  document.addEventListener('focusin', (e) => {
    const t = e.target.closest && e.target.closest('svg [data-k]');
    if (!t) return;
    const html = tipHtml(t.getAttribute('data-k'));
    if (!html) return;
    const r = t.getBoundingClientRect();
    showTip(html, r.right, r.bottom);
  });
  document.addEventListener('focusout', () => hideTip());

  // ------------------------------------------------------------ events
  document.addEventListener('click', (e) => {
    const tab = e.target.closest('.tabs button[data-view]');
    if (tab) { state.view = tab.dataset.view; store.set('view', state.view); render(); return; }
    const opb = e.target.closest('[data-op]');
    if (opb) { state.op = opb.dataset.op; store.set('op', state.op); render(); return; }
    const t = e.target.closest('[data-k]');
    if (t) { open(t.getAttribute('data-k')); }
  });
  document.addEventListener('keydown', (e) => {
    if (e.key !== 'Enter' && e.key !== ' ') return;
    const t = e.target.closest && e.target.closest('svg [data-k]');
    if (t) { e.preventDefault(); open(t.getAttribute('data-k')); }
  });
  document.addEventListener('change', (e) => {
    const t = e.target;
    if (t.matches('[data-sort]')) { state.sort = t.value === 'weight' ? 'weight' : 'name'; store.set('sort', state.sort); render(); }
    else if (t.matches('[data-row]')) { state.row = Number(t.value); render(); }
    else if (t.matches('[data-compare]') && t.value !== '') { open(`p:${t.dataset.compare},${t.value}`); }
  });
  $('back-btn').addEventListener('click', () => { if (state.back.length) { state.panel = state.back.pop(); renderPanel(); } });
  $('close-btn').addEventListener('click', () => { state.back = []; state.panel = null; renderPanel(); });

  const vfToggle = $('vf-toggle');
  function applyVf() {
    document.body.classList.toggle('vf-on', state.vf);
    vfToggle.checked = state.vf;
    $('vf-caption').hidden = !state.vf;
  }
  vfToggle.addEventListener('change', () => { state.vf = vfToggle.checked; store.set('vf', state.vf ? '1' : '0'); applyVf(); });

  const themeBtn = $('theme-btn');
  function applyTheme() {
    const root = document.documentElement;
    if (state.theme === 'light' || state.theme === 'dark') root.setAttribute('data-theme', state.theme);
    else root.removeAttribute('data-theme');
    themeBtn.title = `Theme: ${state.theme === 'auto' ? 'automatic' : state.theme} (click to change)`;
    themeBtn.textContent = state.theme === 'light' ? '☀' : state.theme === 'dark' ? '☾' : '◐';
  }
  themeBtn.addEventListener('click', () => {
    state.theme = state.theme === 'auto' ? 'light' : state.theme === 'light' ? 'dark' : 'auto';
    store.set('theme', state.theme);
    applyTheme();
  });
  let lastNarrow = window.matchMedia('(max-width: 600px)').matches;
  window.addEventListener('resize', () => {
    const nw = window.matchMedia('(max-width: 600px)').matches;
    if (nw !== lastNarrow) { lastNarrow = nw; if (state.view === 'pairs' || state.view === 'tables') render(); }
  });

  // ------------------------------------------------------------ start
  $('stamp').innerHTML = stampText();
  renderAbout();
  const about = $('about');
  if (store.get('about', 'open') === 'closed') about.open = false;
  about.addEventListener('toggle', () => store.set('about', about.open ? 'open' : 'closed'));
  applyTheme();
  applyVf();
  render();
  renderPanel();
})();
