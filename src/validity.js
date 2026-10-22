/* Lógica Axiomática — motor de validez: decide si un argumento es válido en la lógica de cada mundo y,
   si no lo es, construye un contraejemplo que se puede comprobar a mano.
   · clásica y LP proposicionales: todas las valuaciones (2ⁿ o 3ⁿ), con poda;
   · primer orden monádico (clásica y LP): basta un individuo por «tipo», así que también se decide;
   · modal (K, T, K4, S4, S5, GL) e intuicionista proposicionales: método de eliminación de Pratt sobre
     los conjuntos de Hintikka de las subfórmulas, que decide y devuelve un modelo de Kripke;
   · primer orden en general: es indecidible (Church), así que se buscan contramodelos finitos pequeños
     y se intenta cerrar un tableau acotado; si ninguna de las dos cosas funciona, el motor lo reconoce.
   Toda respuesta «inválido» trae un modelo que se vuelve a evaluar antes de mostrarlo, y toda respuesta
   «válido» sale de una búsqueda exhaustiva o de un tableau cerrado. */
(function (root) {
'use strict';
const L = root.Logic;
const { str, subst, subformulas, names, Atom, Bot, Not, And, Or, Imp, Qf } = L;

class Over extends Error {}
const isQ = g => g.t === 'all' || g.t === 'ex';
const isFO = f => subformulas(f).some(g => isQ(g) || (g.t === 'atom' && g.args.length));
const isModal = f => subformulas(f).some(g => g.t === 'box' || g.t === 'dia');
function predsOf(fs) {
  const m = new Map();
  fs.forEach(f => subformulas(f).forEach(g => { if (g.t === 'atom') m.set(g.p, g.args.length); }));
  return m;
}
function nameList(fs) { const s = new Set(); fs.forEach(f => names(f, s)); return [...s].sort(); }
const fresh = (used, k) => [...L.NAMES].filter(n => !used.includes(n)).slice(0, k);
function uniq(fs) { const seen = new Set(); return fs.filter(f => { const k = str(f); if (seen.has(k)) return false; seen.add(k); return true; }); }
/* átomos en el orden en que aparecen: así la búsqueda poda antes */
function atomOrder(fs) {
  const seen = new Set(), out = [];
  const go = g => { if (g.t === 'atom') { const k = str(g); if (!seen.has(k)) { seen.add(k); out.push(k); } } if (g.a) go(g.a); if (g.b) go(g.b); };
  fs.forEach(go);
  return out;
}

/* cambia cada cuantificador por una conjunción o disyunción sobre un dominio finito (dominio constante) */
function ground(f, dom) {
  switch (f.t) {
    case 'all': case 'ex':
      return dom.map(d => ground(subst(f.a, f.v, d), dom)).reduce((x, y) => ({ t: f.t === 'all' ? 'and' : 'or', a: x, b: y }));
    case 'atom': case 'bot': return f;
    case 'not': case 'box': case 'dia': return { t: f.t, a: ground(f.a, dom) };
    default: return { t: f.t, a: ground(f.a, dom), b: ground(f.b, dom) };
  }
}
function groundAtomsOf(fs, dom) {
  const out = [];
  predsOf(fs).forEach((n, p) => {
    let combos = [[]];
    for (let i = 0; i < n; i++) combos = combos.flatMap(c => dom.map(d => [...c, d]));
    combos.forEach(c => out.push(p + c.join('')));
  });
  return out.sort();
}

/* ---------- valores: clásica {0,1} y LP {0,½,1}, con intervalos para valuaciones a medias ---------- */
const U = [0, 1];
function comp(f, idx) {
  switch (f.t) {
    case 'atom': {
      const i = idx.get(str(f));
      return v => { const x = v[i]; return x === undefined ? U : [x, x]; };
    }
    case 'bot': return () => [0, 0];
    case 'not': { const a = comp(f.a, idx); return v => { const x = a(v); return [1 - x[1], 1 - x[0]]; }; }
    case 'and': { const a = comp(f.a, idx), b = comp(f.b, idx); return v => { const x = a(v), y = b(v); return [Math.min(x[0], y[0]), Math.min(x[1], y[1])]; }; }
    case 'or': { const a = comp(f.a, idx), b = comp(f.b, idx); return v => { const x = a(v), y = b(v); return [Math.max(x[0], y[0]), Math.max(x[1], y[1])]; }; }
    case 'imp': { const a = comp(f.a, idx), b = comp(f.b, idx); return v => { const x = a(v), y = b(v); return [Math.max(1 - x[1], y[0]), Math.max(1 - x[0], y[1])]; }; }
    case 'iff': {
      const a = comp(f.a, idx), b = comp(f.b, idx);
      return v => {
        const x = a(v), y = b(v);
        return [Math.min(Math.max(1 - x[1], y[0]), Math.max(1 - y[1], x[0])), Math.min(Math.max(1 - x[0], y[1]), Math.max(1 - y[0], x[1]))];
      };
    }
  }
  throw new Error('comp ' + f.t);
}
/* busca una valuación de atoms que haga designadas las fórmulas de des y no designadas las de und */
function valSearch(des, und, atoms, lp, budget) {
  const vals = lp ? [1, 0.5, 0] : [1, 0], th = lp ? 0.5 : 1;
  const idx = new Map(atoms.map((a, i) => [a, i]));
  const D = des.map(f => comp(f, idx)), N = und.map(f => comp(f, idx));
  const v = new Array(atoms.length);
  let steps = 0;
  const ok = () => D.every(c => c(v)[1] >= th) && N.every(c => c(v)[0] < th);
  const rec = i => {
    if (++steps > budget) throw new Over();
    if (!ok()) return false;
    if (i === atoms.length) return true;
    for (const x of vals) { v[i] = x; if (rec(i + 1)) return true; }
    v[i] = undefined;
    return false;
  };
  if (!rec(0)) return null;
  const out = {};
  atoms.forEach((a, i) => { out[a] = v[i]; });
  return out;
}
const designated = (v, lp) => (lp ? v >= 0.5 : v === 1);
function verifyVal(prem, concl, vals, lp, dom) {
  return prem.every(p => designated(L.evalF(p, vals, dom), lp)) && !designated(L.evalF(concl, vals, dom), lp);
}

/* ---------- primer orden monádico: una valuación por «tipo» de individuo ---------- */
function monadic(prem, concl, lp, budget) {
  const fs = [...prem, concl], P = predsOf(fs);
  if ([...P.values()].some(n => n > 1)) return null;
  const U1 = [...P.keys()].filter(p => P.get(p) === 1).sort(), Z = [...P.keys()].filter(p => P.get(p) === 0).sort();
  const vals = lp ? [1, 0.5, 0] : [1, 0], N = nameList(fs);
  let types = [[]];
  U1.forEach(() => { types = types.flatMap(t => vals.map(x => [...t, x])); });
  const T = types.length;
  if (T > 16 || N.length + T > L.NAMES.length) return null;
  let zs = [[]];
  Z.forEach(() => { zs = zs.flatMap(t => vals.map(x => [...t, x])); });
  if (zs.length * Math.pow(T, N.length) * Math.pow(2, T) > budget) return null;
  const extra = fresh(N, T);
  for (const z of zs) {
    const nt = new Array(N.length).fill(0);
    for (;;) {
      for (let S = N.length ? 0 : 1; S < (1 << T); S++) {
        const dom = N.slice(), v = {};
        Z.forEach((p, i) => { v[p] = z[i]; });
        N.forEach((n, i) => U1.forEach((p, j) => { v[p + n] = types[nt[i]][j]; }));
        let e = 0;
        for (let t = 0; t < T; t++) if (S & (1 << t)) { const d = extra[e++]; dom.push(d); U1.forEach((p, j) => { v[p + d] = types[t][j]; }); }
        if (!designated(L.evalF(concl, v, dom), lp) && prem.every(p => designated(L.evalF(p, v, dom), lp)))
          return { found: { kind: 'fo', dom, atoms: groundAtomsOf(fs, dom), vals: v } };
      }
      let i = 0;
      while (i < N.length && ++nt[i] === T) nt[i++] = 0;
      if (i === N.length) break;
    }
  }
  return { found: null, types: T };
}

/* ---------- Kripke ---------- */
/* evaluación directa en un modelo: W[i] = átomos verdaderos en el mundo i, R[i] = mundos accesibles desde i */
function kEval(f, w, M) {
  switch (f.t) {
    case 'atom': return !!M.W[w][str(f)];
    case 'bot': return false;
    case 'not': return !kEval(f.a, w, M);
    case 'and': return kEval(f.a, w, M) && kEval(f.b, w, M);
    case 'or': return kEval(f.a, w, M) || kEval(f.b, w, M);
    case 'imp': return !kEval(f.a, w, M) || kEval(f.b, w, M);
    case 'iff': return kEval(f.a, w, M) === kEval(f.b, w, M);
    case 'box': return M.R[w].every(v => kEval(f.a, v, M));
    case 'dia': return M.R[w].some(v => kEval(f.a, v, M));
  }
  throw new Error('kEval ' + f.t);
}
/* forzamiento intuicionista: Up[i] = mundos ≥ i (incluido i) */
function iForce(f, w, M) {
  switch (f.t) {
    case 'atom': return !!M.W[w][str(f)];
    case 'bot': return false;
    case 'and': return iForce(f.a, w, M) && iForce(f.b, w, M);
    case 'or': return iForce(f.a, w, M) || iForce(f.b, w, M);
    case 'imp': return M.Up[w].every(v => !iForce(f.a, v, M) || iForce(f.b, v, M));
    case 'not': return M.Up[w].every(v => !iForce(f.a, v, M));
    case 'iff': return M.Up[w].every(v => iForce(f.a, v, M) === iForce(f.b, v, M));
  }
  throw new Error('iForce ' + f.t);
}
function closure(n, edges, refl, trans, sym) {
  const R = Array.from({ length: n }, () => new Set());
  edges.forEach(([a, b]) => { R[a].add(b); if (sym) R[b].add(a); });
  if (refl) for (let i = 0; i < n; i++) R[i].add(i);
  if (trans || sym) {
    let ch = true;
    while (ch) { ch = false; for (let i = 0; i < n; i++) for (const j of [...R[i]]) for (const k of R[j]) if (!R[i].has(k)) { R[i].add(k); ch = true; } }
  }
  return R.map(s => [...s].sort((a, b) => a - b));
}
const FRAME = {
  K: [false, false, false], T: [true, false, false], K4: [false, true, false], S4: [true, true, false], S5: [true, true, true], GL: [false, true, false]
};
const popc = x => { let c = 0; while (x) { c += x & 1; x >>>= 1; } return c; };

/* subfórmulas en orden (hijos antes que padres), sin repetir */
function closureList(fs) {
  const list = [], at = new Map();
  const go = f => {
    const k = str(f);
    if (at.has(k)) return at.get(k);
    const node = { f, t: f.t, a: f.a ? go(f.a) : -1, b: f.b ? go(f.b) : -1 };
    list.push(node); at.set(k, list.length - 1);
    return list.length - 1;
  };
  const roots = fs.map(go);
  return { list, roots };
}
const diaFree = f => {
  switch (f.t) {
    case 'atom': case 'bot': return f;
    case 'dia': return Not({ t: 'box', a: Not(diaFree(f.a)) });
    case 'not': case 'box': return { t: f.t, a: diaFree(f.a) };
    default: return { t: f.t, a: diaFree(f.a), b: diaFree(f.b) };
  }
};
const MAXBITS = 15;

/* Lógica modal proposicional: ¿hay un modelo del sistema sys en el que todas las fórmulas de roots son verdaderas en un mundo? */
function modalSat(roots, sys) {
  const { list, roots: R0 } = closureList(roots.map(diaFree));
  const letters = [], boxes = [];
  list.forEach((n, i) => { if (n.t === 'atom') letters.push(i); if (n.t === 'box') boxes.push(i); });
  const nb = letters.length + boxes.length;
  if (nb > MAXBITS) throw new Over();
  const reflexive = FRAME[sys][0], m = boxes.length;
  const tv = [], boxM = [], bodyM = [];
  const val = new Uint8Array(list.length);
  for (let mask = 0; mask < (1 << nb); mask++) {
    letters.forEach((i, j) => { val[i] = (mask >> j) & 1; });
    boxes.forEach((i, j) => { val[i] = (mask >> (letters.length + j)) & 1; });
    let ok = true;
    for (let i = 0; i < list.length; i++) {
      const n = list[i];
      switch (n.t) {
        case 'bot': val[i] = 0; break;
        case 'not': val[i] = 1 - val[n.a]; break;
        case 'and': val[i] = val[n.a] & val[n.b]; break;
        case 'or': val[i] = val[n.a] | val[n.b]; break;
        case 'imp': val[i] = (1 - val[n.a]) | val[n.b]; break;
        case 'iff': val[i] = val[n.a] === val[n.b] ? 1 : 0; break;
      }
    }
    let bx = 0, bd = 0;
    boxes.forEach((i, j) => { if (val[i]) bx |= 1 << j; if (val[list[i].a]) bd |= 1 << j; });
    if (reflexive && (bx & ~bd)) ok = false;   // T: lo necesario es verdadero aquí
    if (!ok) continue;
    tv.push(val.slice()); boxM.push(bx); bodyM.push(bd);
  }
  const rel = (a, b) => {
    const A = boxM[a], B = boxM[b];
    if (A & ~bodyM[b]) return false;
    if (sys === 'S5') return A === B;
    if (sys === 'K4' || sys === 'S4' || sys === 'GL') { if (A & ~B) return false; }
    if (sys === 'GL' && A === B) return false;
    return true;
  };
  const N = tv.length, alive = new Uint8Array(N).fill(1);
  /* un mundo con ¬□A necesita un sucesor vivo donde A sea falsa; la condición solo depende de sus □ verdaderas */
  let changed = true;
  while (changed) {
    changed = false;
    const memo = new Map();
    for (let a = 0; a < N; a++) {
      if (!alive[a]) continue;
      for (let j = 0; j < m; j++) {
        if (boxM[a] & (1 << j)) continue;
        const key = boxM[a] * 64 + j;
        let has = memo.get(key);
        if (has === undefined) {
          has = false;
          for (let b = 0; b < N && !has; b++) if (alive[b] && !(bodyM[b] & (1 << j)) && rel(a, b)) has = true;
          memo.set(key, has);
        }
        if (!has) { alive[a] = 0; changed = true; break; }
      }
    }
  }
  const sat = a => R0.every(r => tv[a][r]);
  const cands = [];
  for (let a = 0; a < N; a++) if (alive[a] && sat(a)) cands.push(a);
  if (!cands.length) return null;
  cands.sort((x, y) => popc(boxM[x]) - popc(boxM[y]));
  /* modelo pequeño: desde la raíz, un testigo por cada ¬□A, reutilizando mundos cuando se puede */
  const ws = [cands[0]], edges = [];
  for (let q = 0; q < ws.length; q++) {
    const a = ws[q];
    for (let j = 0; j < m; j++) {
      if (boxM[a] & (1 << j)) continue;
      const good = b => alive[b] && !(bodyM[b] & (1 << j)) && rel(a, b);
      let t = ws.findIndex(good);
      if (t < 0) {
        let b = -1;
        for (let c = 0; c < N; c++) if (good(c) && (b < 0 || popc(boxM[c]) < popc(boxM[b]))) b = c;
        if (ws.length >= 9) throw new Over();
        ws.push(b); t = ws.length - 1;
      }
      if (!edges.some(e => e[0] === q && e[1] === t)) edges.push([q, t]);
    }
  }
  const [refl, trans, sym] = FRAME[sys];
  const Rm = closure(ws.length, edges, refl, trans, sym);
  const W = ws.map(a => { const o = {}; letters.forEach(i => { if (tv[a][i]) o[str(list[i].f)] = 1; }); return o; });
  return { W, R: Rm, edges };
}

/* Lógica intuicionista proposicional: ¿hay un modelo de Kripke con un mundo que fuerza todo trues y nada de falses? */
function intSat(trues, falses) {
  const norm = f => {
    switch (f.t) {
      case 'atom': case 'bot': return f;
      case 'not': return Imp(norm(f.a), Bot);
      case 'iff': { const a = norm(f.a), b = norm(f.b); return And(Imp(a, b), Imp(b, a)); }
      default: return { t: f.t, a: norm(f.a), b: norm(f.b) };
    }
  };
  const T0 = trues.map(norm), F0 = falses.map(norm);
  const { list, roots } = closureList([...T0, ...F0]);
  const nT = T0.length;
  const bits = [], imps = [];
  list.forEach((n, i) => { if (n.t === 'atom' || n.t === 'imp') bits.push(i); if (n.t === 'imp') imps.push(i); });
  const nb = bits.length;
  if (nb > MAXBITS) throw new Over();
  const S = 1 << nb, okA = new Uint8Array(S), tv = new Array(S);
  const val = new Uint8Array(list.length);
  for (let mask = 0; mask < S; mask++) {
    bits.forEach((i, j) => { val[i] = (mask >> j) & 1; });
    for (let i = 0; i < list.length; i++) {
      const n = list[i];
      if (n.t === 'bot') val[i] = 0;
      else if (n.t === 'and') val[i] = val[n.a] & val[n.b];
      else if (n.t === 'or') val[i] = val[n.a] | val[n.b];
    }
    let ok = true;
    for (const i of imps) {
      const n = list[i];
      if (val[i] && val[n.a] && !val[n.b]) ok = false;   // A→B verdadera: aquí no puede darse A sin B
      if (!val[i] && val[n.b]) ok = false;               // si B ya vale, A→B también
    }
    if (ok) { okA[mask] = 1; tv[mask] = val.slice(); }
  }
  const alive = okA.slice();
  const bitOf = new Map(bits.map((i, j) => [i, j]));
  /* sup[m] = 1 si algún mundo vivo de W contiene a m: suma sobre superconjuntos */
  const upSet = pred => {
    const g = new Uint8Array(S);
    for (let x = 0; x < S; x++) if (alive[x] && pred(x)) g[x] = 1;
    for (let j = 0; j < nb; j++) for (let x = 0; x < S; x++) if (!(x & (1 << j)) && g[x | (1 << j)]) g[x] = 1;
    return g;
  };
  let changed = true;
  while (changed) {
    changed = false;
    const wit = imps.map(i => { const n = list[i]; return upSet(x => tv[x][n.a] && !tv[x][n.b]); });
    for (let x = 0; x < S; x++) {
      if (!alive[x]) continue;
      for (let k = 0; k < imps.length; k++) {
        if (x & (1 << bitOf.get(imps[k]))) continue;
        if (!wit[k][x]) { alive[x] = 0; changed = true; break; }
      }
    }
  }
  const sat = x => roots.every((r, i) => (i < nT ? tv[x][r] : !tv[x][r]));
  let r0 = -1;
  for (let x = 0; x < S; x++) if (alive[x] && sat(x) && (r0 < 0 || popc(x) < popc(r0))) r0 = x;
  if (r0 < 0) return null;
  const ws = [r0], edges = [];
  for (let q = 0; q < ws.length; q++) {
    const a = ws[q];
    imps.forEach(i => {
      if (a & (1 << bitOf.get(i))) return;
      const n = list[i];
      const good = b => alive[b] && (b & a) === a && tv[b][n.a] && !tv[b][n.b];
      if (good(a)) return;
      let t = ws.findIndex(b => good(b) && ws.indexOf(b) !== q);
      if (t < 0) {
        let b = -1;
        for (let c = 0; c < S; c++) if (good(c) && (b < 0 || popc(c) < popc(b))) b = c;
        if (ws.length >= 9) throw new Over();
        ws.push(b); t = ws.length - 1;
      }
      if (!edges.some(e => e[0] === q && e[1] === t)) edges.push([q, t]);
    });
  }
  /* el orden es la inclusión entre mundos elegidos (contiene las aristas de testigo) */
  const Up = ws.map(a => ws.map((b, j) => ((b & a) === a ? j : -1)).filter(j => j >= 0));
  const W = ws.map(a => { const o = {}; bits.forEach(i => { if (list[i].t === 'atom' && tv[a][i]) o[str(list[i].f)] = 1; }); return o; });
  /* aristas para dibujar: las coberturas del orden (sin las que se deducen por transitividad) */
  const lt = (i, j) => i !== j && Up[i].includes(j) && !Up[j].includes(i);
  const hasse = [];
  for (let i = 0; i < ws.length; i++) for (let j = 0; j < ws.length; j++)
    if (lt(i, j) && !ws.some((_, k) => lt(i, k) && lt(k, j))) hasse.push([i, j]);
  return { W, Up, edges: hasse };
}

/* ---------- tableau etiquetado y acotado (clásica, modal de dominio constante, intuicionista) ---------- */
function tableau(roots, mode, sys, lim, used) {
  let steps = 0;
  const pool = [...L.NAMES].filter(n => !used.includes(n));
  const keyOf = (s, w, f) => (s ? 'T' : 'F') + w + '|' + str(f);
  const br0 = { nodes: [], key: new Set(), worlds: [{ par: -1, c: used.slice() }], gc: used.slice(), done: new Set(), closed: false, nc: 0, hit: false };
  const clone = b => ({ nodes: b.nodes.slice(), key: new Set(b.key), worlds: b.worlds.map(w => ({ par: w.par, c: w.c.slice() })), gc: b.gc.slice(), done: new Set(b.done), closed: b.closed, nc: b.nc, hit: b.hit });
  const anc = (b, w) => { const o = []; for (let x = w; x >= 0; x = b.worlds[x].par) o.push(x); return o; };
  const up = (b, w) => b.worlds.map((_, v) => v).filter(v => anc(b, v).includes(w));
  const acc = (b, w) => {
    const [refl, trans, sym] = FRAME[sys || 'K'];
    const edges = b.worlds.map((x, v) => [x.par, v]).filter(e => e[0] >= 0);
    return closure(b.worlds.length, edges, refl, trans, sym)[w];
  };
  const dom = (b, w) => (mode === 'int' ? [...new Set(anc(b, w).flatMap(x => b.worlds[x].c))] : b.gc);
  function add(b, s, f, w) {
    const k = keyOf(s, w, f);
    if (b.key.has(k)) return;
    b.key.add(k); b.nodes.push({ s, f, w });
    if (s && f.t === 'bot') { b.closed = true; return; }
    if (mode === 'int') {
      if (s) { if (up(b, w).some(v => b.key.has(keyOf(false, v, f)))) b.closed = true; }
      else if (anc(b, w).some(u => b.key.has(keyOf(true, u, f)))) b.closed = true;
    } else if (b.key.has(keyOf(!s, w, f))) b.closed = true;
  }
  function newConst(b, w) {
    if (b.nc >= lim.c) { b.hit = true; return null; }
    const c = pool[b.nc++];
    if (mode === 'int') b.worlds[w].c.push(c); else b.gc.push(c);
    return c;
  }
  function newWorld(b, w) {
    if (b.worlds.length >= lim.w) { b.hit = true; return -1; }
    b.worlds.push({ par: w, c: [] });
    return b.worlds.length - 1;
  }
  /* ¿añadir este nodo cerraría la rama? */
  function clash(b, s, f, w) {
    if (s && f.t === 'bot') return true;
    if (mode !== 'int') return b.key.has(keyOf(!s, w, f));
    return s ? up(b, w).some(v => b.key.has(keyOf(false, v, f))) : anc(b, w).some(u => b.key.has(keyOf(true, u, f)));
  }
  const holds = (b, s, f, v) => (mode === 'int' && s ? anc(b, v).some(u => b.key.has(keyOf(true, u, f))) : b.key.has(keyOf(s, v, f)));
  /* un mundo ya existente sirve de testigo: basta con no crear otro (saltarse una regla nunca cierra ramas de más) */
  function witnessed(b, nd, k) {
    const ws = mode === 'int' ? up(b, nd.w) : acc(b, nd.w);
    if (k.p === 'w') return ws.some(v => k.add.every(([s, g]) => holds(b, s, g, v)));
    return ws.some(v => dom(b, v).some(c => holds(b, false, subst(nd.f.a, nd.f.v, c), v)));
  }
  /* qué hace cada nodo: a = α (añade), b = β (ramifica), n = ν (a mundos accesibles), g = γ (a cada individuo), p = π/δ (crea) */
  function kind(s, f) {
    const I = mode === 'int';
    switch (f.t) {
      case 'not': return I ? (s ? { n: [[false, f.a]] } : { p: 'w', add: [[true, f.a]] }) : { a: [[!s, f.a]] };
      case 'and': return s ? { a: [[true, f.a], [true, f.b]] } : { b: [[[false, f.a]], [[false, f.b]]] };
      case 'or': return s ? { b: [[[true, f.a]], [[true, f.b]]] } : { a: [[false, f.a], [false, f.b]] };
      case 'imp':
        if (I) return s ? { bn: [[[false, f.a]], [[true, f.b]]] } : { p: 'w', add: [[true, f.a], [false, f.b]] };
        return s ? { b: [[[false, f.a]], [[true, f.b]]] } : { a: [[true, f.a], [false, f.b]] };
      case 'iff': return s ? { b: [[[true, f.a], [true, f.b]], [[false, f.a], [false, f.b]]] } : { b: [[[true, f.a], [false, f.b]], [[false, f.a], [true, f.b]]] };
      case 'box': return s ? { n: [[true, f.a]] } : { p: 'w', add: [[false, f.a]] };
      case 'dia': return s ? { p: 'w', add: [[true, f.a]] } : { n: [[false, f.a]] };
      case 'all': return s ? { g: true } : { p: I ? 'wc' : 'c' };
      case 'ex': return s ? { p: 'c' } : { g: true, local: true };
    }
    return {};
  }
  function run(b) {
    for (;;) {
      if (++steps > lim.steps) throw new Over();
      if (b.closed) return true;
      if (b.nodes.length > lim.n) { b.hit = true; return false; }
      let act = null;
      /* 1. α */
      for (let i = 0; i < b.nodes.length && !act; i++) {
        const nd = b.nodes[i], k = kind(nd.s, nd.f);
        if (k.a && !b.done.has('a' + i)) act = () => { b.done.add('a' + i); k.a.forEach(([s, g]) => add(b, s, g, nd.w)); };
      }
      /* 2. ν: a cada mundo accesible (o posterior, en la intuicionista) */
      for (let i = 0; i < b.nodes.length && !act; i++) {
        const nd = b.nodes[i], k = kind(nd.s, nd.f);
        if (!k.n) continue;
        const ws = mode === 'int' ? up(b, nd.w) : acc(b, nd.w);
        for (const v of ws) if (!b.done.has('n' + i + '@' + v)) { act = () => { b.done.add('n' + i + '@' + v); k.n.forEach(([s, g]) => add(b, s, g, v)); }; break; }
      }
      /* 3. δ: individuos nuevos para ∃ verdaderos y ∀ falsos, por orden de llegada */
      for (let i = 0; i < b.nodes.length && !act; i++) {
        const nd = b.nodes[i], k = kind(nd.s, nd.f);
        if (k.p !== 'c' || b.done.has('p' + i)) continue;
        act = () => { b.done.add('p' + i); const c = newConst(b, nd.w); if (c != null) add(b, nd.s, subst(nd.f.a, nd.f.v, c), nd.w); };
      }
      /* 4. γ sobre los individuos que ya hay */
      let needDom = false;
      for (let i = 0; i < b.nodes.length && !act; i++) {
        const nd = b.nodes[i], k = kind(nd.s, nd.f);
        if (!k.g) continue;
        const ws = mode === 'int' && !k.local ? up(b, nd.w) : [nd.w];
        for (const v of ws) {
          let D = dom(b, v);
          if (!D.length) { needDom = true; continue; }   // el individuo cualquiera se inventa al final: antes, los testigos
          const c = D.find(x => !b.done.has('g' + i + '@' + v + ':' + x));
          if (c != null) { act = () => { b.done.add('g' + i + '@' + v + ':' + c); add(b, nd.s, subst(nd.f.a, nd.f.v, c), v); }; break; }
        }
      }
      if (act) { act(); continue; }
      /* 5. β: se ramifica; primero donde alguna alternativa se cierra en el acto (casi como un paso α) */
      let best = null;
      for (let i = 0; i < b.nodes.length; i++) {
        const nd = b.nodes[i], k = kind(nd.s, nd.f);
        if (!k.b && !k.bn) continue;
        const ws = k.bn ? up(b, nd.w) : [nd.w];
        for (const v of ws) {
          const id = 'b' + i + '@' + v;
          if (b.done.has(id)) continue;
          const alts = (k.b || k.bn).filter(alt => !alt.some(([s, g]) => clash(b, s, g, v)));
          if (!best || alts.length < best.alts.length) best = { id, v, alts };
          if (alts.length <= 1) break;
        }
        if (best && best.alts.length <= 1) break;
      }
      if (best) {
        for (const alt of best.alts) {
          const c = clone(b);
          c.done.add(best.id);
          alt.forEach(([s, g]) => add(c, s, g, best.v));
          if (!run(c)) return false;
        }
        return true;
      }
      /* 6. π: mundos nuevos, primero para los mundos menos profundos (así ninguna obligación espera para siempre);
         no se crea nada si ya hay un testigo */
      const depth = w => anc(b, w).length;
      let pick = -1;
      for (let i = 0; i < b.nodes.length; i++) {
        const nd = b.nodes[i], k = kind(nd.s, nd.f);
        if (!k.p || k.p === 'c' || b.done.has('p' + i)) continue;
        if (witnessed(b, nd, k)) { b.done.add('p' + i); continue; }
        if (pick < 0 || depth(nd.w) < depth(b.nodes[pick].w)) pick = i;
      }
      if (pick >= 0) {
        const i = pick, nd = b.nodes[i], k = kind(nd.s, nd.f);
        act = () => {
          b.done.add('p' + i);
          if (k.p === 'w') { const v = newWorld(b, nd.w); if (v >= 0) k.add.forEach(([s, g]) => add(b, s, g, v)); }
          else { const v = newWorld(b, nd.w); if (v >= 0) { const c = newConst(b, v); if (c != null) add(b, false, subst(nd.f.a, nd.f.v, c), v); } }
        };
      }
      if (act) { act(); continue; }
      /* los dominios no son vacíos: si un ∀ verdadero o un ∃ falso no tiene a quién aplicarse, se toma un individuo cualquiera */
      if (needDom && newConst(b, 0) != null) continue;
      return false;
    }
  }
  /* en la intuicionista A↔B no se comporta como en la tabla clásica: se trata como (A→B)∧(B→A) */
  const unIff = f => {
    switch (f.t) {
      case 'atom': case 'bot': return f;
      case 'iff': { const a = unIff(f.a), b = unIff(f.b); return And(Imp(a, b), Imp(b, a)); }
      case 'all': case 'ex': return Qf(f.t, f.v, unIff(f.a));
      case 'not': case 'box': case 'dia': return { t: f.t, a: unIff(f.a) };
      default: return { t: f.t, a: unIff(f.a), b: unIff(f.b) };
    }
  };
  roots.forEach(([s, f]) => add(br0, s, mode === 'int' ? unIff(f) : f, 0));
  return run(br0);
}

/* LP de primer orden → clásica: cada predicado F se parte en F⁺ (F es verdadera) y F⁻ (F es falsa) */
function nnf(f, pos) {
  switch (f.t) {
    case 'atom': return pos ? f : Not(f);
    case 'bot': return pos ? Bot : Not(Bot);
    case 'not': return nnf(f.a, !pos);
    case 'and': return pos ? And(nnf(f.a, true), nnf(f.b, true)) : Or(nnf(f.a, false), nnf(f.b, false));
    case 'or': return pos ? Or(nnf(f.a, true), nnf(f.b, true)) : And(nnf(f.a, false), nnf(f.b, false));
    case 'imp': return pos ? Or(nnf(f.a, false), nnf(f.b, true)) : And(nnf(f.a, true), nnf(f.b, false));
    case 'iff': return pos ? And(Or(nnf(f.a, false), nnf(f.b, true)), Or(nnf(f.b, false), nnf(f.a, true)))
      : Or(And(nnf(f.a, true), nnf(f.b, false)), And(nnf(f.b, true), nnf(f.a, false)));
    case 'all': return Qf(pos ? 'all' : 'ex', f.v, nnf(f.a, pos));
    case 'ex': return Qf(pos ? 'ex' : 'all', f.v, nnf(f.a, pos));
  }
  throw new Error('nnf ' + f.t);
}
function splitLP(f) {
  switch (f.t) {
    case 'atom': return Atom(f.p + '⁺', f.args);
    case 'not': return f.a.t === 'atom' ? Atom(f.a.p + '⁻', f.a.args) : f;
    case 'bot': return f;
    case 'all': case 'ex': return Qf(f.t, f.v, splitLP(f.a));
    default: return { t: f.t, a: splitLP(f.a), b: splitLP(f.b) };
  }
}
function lpToClassical(prem, concl) {
  const P = predsOf([...prem, concl]), ex = [];
  P.forEach((n, p) => {
    const vs = [...L.VARS].slice(0, n);
    let f = Or(Atom(p + '⁺', vs), Atom(p + '⁻', vs));
    vs.slice().reverse().forEach(v => { f = Qf('all', v, f); });
    ex.push(f);
  });
  return { prem: [...ex, ...prem.map(f => splitLP(nnf(f, true)))], concl: splitLP(nnf(concl, true)) };
}

/* ---------- decisión ---------- */
/* logic: 'cl' clásica · 'lp' · 'modal' (sys: K, T, K4, S4, S5, GL) · 'int' intuicionista.
   Devuelve { v: 'valid' | 'invalid' | 'unknown', how, model, rows } */
function check(logic, sys, prem, concl) {
  const fs = [...prem, concl];
  const fo = fs.some(isFO), N = nameList(fs);
  const lp = logic === 'lp';
  if (logic === 'cl' || lp) {
    if (!fo) {
      const atoms = atomOrder([concl, ...prem]);
      if (atoms.length > (lp ? 9 : 14)) return { v: 'unknown', how: 'big' };
      const m = valSearch(prem, [concl], atoms, lp, 2e6);
      if (m && !verifyVal(prem, concl, m, lp)) throw new Error('contraejemplo que no lo es');
      return m ? { v: 'invalid', how: 'table', model: { kind: 'val', atoms: atoms.slice().sort(), vals: m } } : { v: 'valid', how: 'table', rows: Math.pow(lp ? 3 : 2, atoms.length) };
    }
    const t = lp ? lpToClassical(prem, concl) : { prem, concl }, tu = nameList([...t.prem, t.concl]);
    if (tryTableau(t.prem, t.concl, 'cl', null, tu, 0, 1)) return { v: 'valid', how: 'tableau' };
    const mo = monadic(prem, concl, lp, 4e5);
    if (mo) {
      if (mo.found) {
        if (!verifyVal(prem, concl, mo.found.vals, lp, mo.found.dom)) throw new Error('contramodelo monádico que no lo es');
        return { v: 'invalid', how: 'monadic', model: shrinkFO(mo.found, prem, concl, lp) };
      }
      return { v: 'valid', how: 'monadic', types: mo.types };
    }
    /* poliádica: tableau acotado y contramodelos pequeños */
    if (tryTableau(t.prem, t.concl, 'cl', null, tu, 1, 2)) return { v: 'valid', how: 'tableau' };
    const cm = groundSearch(prem, concl, lp, N);
    if (cm) return { v: 'invalid', how: 'finite', model: cm };
    if (tryTableau(t.prem, t.concl, 'cl', null, tu, 2)) return { v: 'valid', how: 'tableau' };
    return { v: 'unknown', how: 'fo' };
  }
  if (logic === 'modal') {
    if (!fo) {
      try {
        const M = modalSat([...prem, Not(concl)], sys);
        if (!M) return { v: 'valid', how: 'kripke' };
        if (!(prem.every(p => kEval(p, 0, M)) && !kEval(concl, 0, M))) throw new Error('modelo de Kripke que no lo es');
        return { v: 'invalid', how: 'kripke', model: Object.assign({ kind: 'kripke', sys }, M) };
      } catch (e) { if (!(e instanceof Over)) throw e; return tryTableau(prem, concl, 'cl', sys, []) ? { v: 'valid', how: 'tableau' } : { v: 'unknown', how: 'big' }; }
    }
    if (tryTableau(prem, concl, 'cl', sys, N)) return { v: 'valid', how: 'tableau' };
    for (let n = Math.max(1, N.length); n <= N.length + 2; n++) {
      const dom = [...N, ...fresh(N, n - N.length)];
      try {
        const M = modalSat([...prem, Not(concl)].map(f => ground(f, dom)), sys);
        if (M) {
          const gp = prem.map(f => ground(f, dom)), gc = ground(concl, dom);
          if (!(gp.every(p => kEval(p, 0, M)) && !kEval(gc, 0, M))) throw new Error('modelo de Kripke que no lo es');
          return { v: 'invalid', how: 'kripke', model: Object.assign({ kind: 'kripke', sys, dom }, M) };
        }
      } catch (e) { if (!(e instanceof Over)) throw e; break; }
    }
    return { v: 'unknown', how: 'fo' };
  }
  if (logic === 'int') {
    if (!fo) {
      try {
        const M = intSat(prem, [concl]);
        if (!M) return { v: 'valid', how: 'kripke' };
        if (!(prem.every(p => iForce(p, 0, M)) && !iForce(concl, 0, M))) throw new Error('modelo intuicionista que no lo es');
        return { v: 'invalid', how: 'kripke', model: Object.assign({ kind: 'int' }, M) };
      } catch (e) { if (!(e instanceof Over)) throw e; return tryTableau(prem, concl, 'int', null, []) ? { v: 'valid', how: 'tableau' } : { v: 'unknown', how: 'big' }; }
    }
    if (tryTableau(prem, concl, 'int', null, N)) return { v: 'valid', how: 'tableau' };
    for (let n = Math.max(1, N.length); n <= N.length + 2; n++) {
      const dom = [...N, ...fresh(N, n - N.length)];
      try {
        const gp = prem.map(f => ground(f, dom)), gc = ground(concl, dom);
        const M = intSat(gp, [gc]);
        if (M) {
          if (!(gp.every(p => iForce(p, 0, M)) && !iForce(gc, 0, M))) throw new Error('modelo intuicionista que no lo es');
          return { v: 'invalid', how: 'kripke', model: Object.assign({ kind: 'int', dom }, M) };
        }
      } catch (e) { if (!(e instanceof Over)) throw e; break; }
    }
    return { v: 'unknown', how: 'fo' };
  }
  throw new Error('lógica desconocida ' + logic);
}
const LIMS = [{ w: 4, c: 3, n: 160, steps: 4e4 }, { w: 6, c: 4, n: 300, steps: 1e5 }, { w: 8, c: 5, n: 500, steps: 3e5 }];
function tryTableau(prem, concl, mode, sys, used, from, to) {
  const roots = [...prem.map(f => [true, f]), [false, concl]];
  for (const lim of LIMS.slice(from || 0, to || LIMS.length)) {
    try { if (tableau(roots, mode, sys, lim, used)) return true; } catch (e) { if (!(e instanceof Over)) throw e; }
  }
  return false;
}
function groundSearch(prem, concl, lp, N) {
  for (let n = Math.max(1, N.length); n <= N.length + 3; n++) {
    const dom = [...N, ...fresh(N, n - N.length)];
    const gp = prem.map(f => ground(f, dom)), gc = ground(concl, dom);
    const atoms = atomOrder([gc, ...gp]);
    if (atoms.length > 40) break;
    let m = null;
    try { m = valSearch(gp, [gc], atoms, lp, 3e5); } catch (e) { if (!(e instanceof Over)) throw e; break; }
    if (m) {
      groundAtomsOf([...prem, concl], dom).forEach(a => { if (m[a] === undefined) m[a] = 0; });
      if (!verifyVal(prem, concl, m, lp, dom)) throw new Error('contramodelo finito que no lo es');
      return shrinkFO({ kind: 'fo', dom, atoms: groundAtomsOf([...prem, concl], dom), vals: m }, prem, concl, lp);
    }
  }
  return null;
}
/* quita individuos que sobran (sin nombre) mientras el contramodelo siga funcionando */
function shrinkFO(M, prem, concl, lp) {
  const N = nameList([...prem, concl]);
  let dom = M.dom.slice();
  for (const d of M.dom.slice().reverse()) {
    if (N.includes(d) || dom.length <= 1) continue;
    const d2 = dom.filter(x => x !== d);
    if (verifyVal(prem, concl, M.vals, lp, d2)) dom = d2;
  }
  const atoms = groundAtomsOf([...prem, concl], dom), vals = {};
  atoms.forEach(a => { vals[a] = M.vals[a] === undefined ? 0 : M.vals[a]; });
  Object.keys(M.vals).forEach(a => { if (!a.slice(1).length) vals[a] = M.vals[a]; });
  return { kind: 'fo', dom, atoms, vals };
}

root.Validity = { check, kEval, iForce, ground, tableau, Over };
})(typeof window !== 'undefined' ? window : globalThis);
