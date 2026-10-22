/* Lógica Axiomática — núcleo lógico: fórmulas, cálculo de Hilbert y reglas derivadas */
(function (root) {
'use strict';

const VARS = 'xyzwuv';
const NAMES = 'abcdefghijklmnopqrst';
const isVar = c => VARS.includes(c);

class LErr extends Error {}
const fail = m => { throw new LErr(m); };

/* ---------- fórmulas ---------- */
const Atom = (p, args) => ({ t: 'atom', p, args: args || [] });
const Bot = { t: 'bot' };
const Not = a => ({ t: 'not', a });
const Box = a => ({ t: 'box', a });
const Dia = a => ({ t: 'dia', a });
const Bin = (t, a, b) => ({ t, a, b });
const And = (a, b) => Bin('and', a, b);
const Or = (a, b) => Bin('or', a, b);
const Imp = (a, b) => Bin('imp', a, b);
const Iff = (a, b) => Bin('iff', a, b);
const Qf = (t, v, a) => ({ t, v, a });
const BIN = { and: '∧', or: '∨', imp: '→', iff: '↔' };

function str(f, top) {
  switch (f.t) {
    case 'atom': return f.p + f.args.join('');
    case 'bot': return '⊥';
    case 'not': return '¬' + str(f.a, false);
    case 'box': return '□' + str(f.a, false);
    case 'dia': return '◇' + str(f.a, false);
    case 'all': return '∀' + f.v + str(f.a, false);
    case 'ex': return '∃' + f.v + str(f.a, false);
    default: {
      const s = str(f.a, false) + BIN[f.t] + str(f.b, false);
      return top === false ? '(' + s + ')' : s;
    }
  }
}
const eq = (a, b) => str(a) === str(b);

function parse(src) {
  const s = String(src)
    .replace(/<->/g, '↔').replace(/->/g, '→').replace(/\[\]/g, '□').replace(/<>/g, '◇')
    .replace(/~/g, '¬').replace(/&/g, '∧').replace(/\|/g, '∨').replace(/#/g, '⊥')
    .replace(/\s+/g, '');
  let i = 0;
  const eat = c => (s[i] === c ? (i++, true) : false);
  function iff() { let a = imp(); while (eat('↔')) a = Iff(a, imp()); return a; }
  function imp() { const a = or(); return eat('→') ? Imp(a, imp()) : a; }
  function or() { let a = and(); while (eat('∨')) a = Or(a, and()); return a; }
  function and() { let a = un(); while (eat('∧')) a = And(a, un()); return a; }
  function un() {
    const c = s[i];
    if (c === '¬') { i++; return Not(un()); }
    if (c === '□') { i++; return Box(un()); }
    if (c === '◇') { i++; return Dia(un()); }
    if (c === '∀' || c === '∃') {
      i++;
      const v = s[i];
      if (!v || !isVar(v)) fail('Después de ' + c + ' va una variable (x, y, z).');
      i++;
      return Qf(c === '∀' ? 'all' : 'ex', v, un());
    }
    if (c === '⊥') { i++; return Bot; }
    if (c === '(') {
      i++;
      const a = iff();
      if (!eat(')')) fail('Falta cerrar un paréntesis.');
      return a;
    }
    if (c && c >= 'A' && c <= 'Z') {
      i++;
      const args = [];
      while (s[i] && s[i] >= 'a' && s[i] <= 'z') args.push(s[i++]);
      return Atom(c, args);
    }
    fail(c ? 'No esperaba «' + c + '» ahí.' : 'La fórmula está incompleta.');
  }
  if (!s) fail('Escribe una fórmula.');
  const f = iff();
  if (i < s.length) fail('No esperaba «' + s[i] + '» ahí.');
  return f;
}

function subformulas(f, out) {
  out = out || [];
  out.push(f);
  if (f.a) subformulas(f.a, out);
  if (f.b) subformulas(f.b, out);
  return out;
}
function size(f) { return subformulas(f).length; }

function names(f, out) {
  out = out || new Set();
  if (f.t === 'atom') f.args.forEach(a => { if (!isVar(a)) out.add(a); });
  if (f.a) names(f.a, out);
  if (f.b) names(f.b, out);
  return out;
}
function varsOf(f, out) {
  out = out || new Set();
  if (f.t === 'atom') f.args.forEach(a => { if (isVar(a)) out.add(a); });
  if (f.v) out.add(f.v);
  if (f.a) varsOf(f.a, out);
  if (f.b) varsOf(f.b, out);
  return out;
}
function freeVars(f, bound, out) {
  bound = bound || new Set(); out = out || new Set();
  if (f.t === 'atom') f.args.forEach(a => { if (isVar(a) && !bound.has(a)) out.add(a); });
  else if (f.t === 'all' || f.t === 'ex') { const b2 = new Set(bound); b2.add(f.v); freeVars(f.a, b2, out); }
  else { if (f.a) freeVars(f.a, bound, out); if (f.b) freeVars(f.b, bound, out); }
  return out;
}
const closed = f => freeVars(f).size === 0;

function subst(f, v, t) {
  switch (f.t) {
    case 'atom': return Atom(f.p, f.args.map(a => (a === v ? t : a)));
    case 'bot': return f;
    case 'not': case 'box': case 'dia': return { t: f.t, a: subst(f.a, v, t) };
    case 'all': case 'ex': return f.v === v ? f : Qf(f.t, f.v, subst(f.a, v, t));
    default: return Bin(f.t, subst(f.a, v, t), subst(f.b, v, t));
  }
}
function countName(f, c) {
  let k = 0;
  subformulas(f).forEach(g => { if (g.t === 'atom') g.args.forEach(a => { if (a === c) k++; }); });
  return k;
}
/* cambia apariciones del nombre c por la variable v; mask elige cuáles (bit i = aparición i) */
function replName(f, c, v, mask) {
  let k = 0;
  const go = g => {
    switch (g.t) {
      case 'atom': return Atom(g.p, g.args.map(a => {
        if (a !== c) return a;
        const bit = 1 << k++;
        return mask & bit ? v : a;
      }));
      case 'bot': return g;
      case 'not': case 'box': case 'dia': return { t: g.t, a: go(g.a) };
      case 'all': case 'ex': return Qf(g.t, g.v, go(g.a));
      default: { const a = go(g.a); return Bin(g.t, a, go(g.b)); }
    }
  };
  return go(f);
}
/* ¿inst es instancia de Qx A? → nombre usado, null si la variable no aparece, false si no lo es */
function instName(q, inst) {
  if (!freeVars(q.a).has(q.v)) return eq(q.a, inst) ? null : false;
  for (const n of names(inst)) if (eq(subst(q.a, q.v, n), inst)) return n;
  return false;
}

/* ---------- semántica de valores (clásica y LP) ---------- */
/* dom: los individuos del dominio (nombres), para evaluar cuantificadores en un dominio finito */
function evalF(f, v, dom) {
  switch (f.t) {
    case 'atom': return v[str(f)];
    case 'bot': return 0;
    case 'not': return 1 - evalF(f.a, v, dom);
    case 'and': return Math.min(evalF(f.a, v, dom), evalF(f.b, v, dom));
    case 'or': return Math.max(evalF(f.a, v, dom), evalF(f.b, v, dom));
    case 'imp': return Math.max(1 - evalF(f.a, v, dom), evalF(f.b, v, dom));
    case 'iff': { const a = evalF(f.a, v, dom), b = evalF(f.b, v, dom); return Math.min(Math.max(1 - a, b), Math.max(1 - b, a)); }
    case 'all': if (dom) return Math.min(...dom.map(d => evalF(subst(f.a, f.v, d), v, dom))); break;
    case 'ex': if (dom) return Math.max(...dom.map(d => evalF(subst(f.a, f.v, d), v, dom))); break;
  }
  fail('Fórmula no evaluable');
}
/* átomos básicos de un dominio finito: cada predicado aplicado a cada combinación de individuos */
function groundAtoms(fs, dom) {
  const preds = new Map();
  fs.forEach(f => subformulas(f).forEach(g => { if (g.t === 'atom') preds.set(g.p, g.args.length); }));
  const out = [];
  [...preds.keys()].sort().forEach(p => {
    let combos = [[]];
    for (let i = 0; i < preds.get(p); i++) combos = combos.flatMap(c => dom.map(d => [...c, d]));
    combos.forEach(c => out.push(p + c.join('')));
  });
  return out;
}
function atomsOf(fs) {
  const s = new Set();
  fs.forEach(f => subformulas(f).forEach(g => { if (g.t === 'atom') s.add(str(g)); }));
  return [...s].sort();
}

/* ---------- estado de la prueba ----------
   Cada línea guarda de qué premisas y supuestos depende (deps, índices de línea): un axioma no depende de nada,
   una premisa o un supuesto depende de sí mismo, y cada paso hereda las dependencias de las líneas que cita.
   La necesitación solo se aplica a líneas sin dependencias, es decir, a teoremas. */
function newProof(premises) {
  const st = { lines: [], subs: {}, open: [], nid: 1 };
  premises.forEach((f, i) => st.lines.push({ f, kind: 'prem', rule: 'Premisa', cites: '', path: [], deps: [i] }));
  return st;
}
const clone = st => JSON.parse(JSON.stringify(st));

function addHyp(st, f) {
  st = clone(st);
  const id = st.nid++;
  st.subs[id] = { id, kind: 'hyp', start: st.lines.length, end: null, parent: st.open.slice() };
  st.open.push(id);
  st.lines.push({ f: f || null, kind: 'hyp', rule: 'Supuesto', cites: '', path: st.open.slice(), deps: [st.lines.length] });
  return st;
}
function closeSub(st) {
  if (!st.open.length) fail('No hay ninguna subprueba abierta.');
  st = clone(st);
  const id = st.open.pop();
  st.subs[id].end = st.lines.length - 1;
  return st;
}

function isPrefix(p, S) {
  if (p.length > S.length) return false;
  for (let i = 0; i < p.length; i++) if (p[i] !== S[i]) return false;
  return true;
}
/* 0 si la línea i se puede citar desde la posición S; -1 si queda dentro de una subprueba cerrada o ajena */
function lineK(st, i, S) { return isPrefix(st.lines[i].path, S) ? 0 : -1; }
function subK(st, sp, S) { return sp.end != null && isPrefix(sp.parent, S) ? 0 : -1; }
function subAt(st, lineNo) {
  for (const id in st.subs) if (st.subs[id].start === lineNo - 1) return st.subs[id];
  return null;
}
/* subprueba cerrada (la más externa) que contiene la línea i y que se puede citar desde aquí */
function pickSub(st, i) {
  for (const id of st.lines[i].path) {
    const sp = st.subs[id];
    if (sp.end != null) return subK(st, sp, st.open) === 0 ? sp : null;
  }
  return null;
}
function subInfo(st, sp) {
  const endIdx = sp.end == null ? st.lines.length - 1 : sp.end;
  const first = st.lines[sp.start], last = st.lines[endIdx];
  const direct = last.path.length === sp.parent.length + 1;
  return {
    sp, open: sp.end == null, hypIdx: sp.start, lastIdx: endIdx,
    hyp: first.f,
    last: direct && last.f ? last.f : null,
    ref: (sp.start + 1) + '–' + (endIdx + 1)
  };
}
function openHyps(st, base) {
  const out = st.lines.filter(l => l.kind === 'prem').map(l => l.f);
  base.forEach(id => out.push(st.lines[st.subs[id].start].f));
  return out;
}
function namesInPlay(st, goal) {
  const s = new Set();
  st.lines.forEach(l => { if (l.f) names(l.f, s); });
  if (goal) names(goal, s);
  return [...s].sort();
}
function freshName(st, goal) {
  const used = namesInPlay(st, goal);
  return [...NAMES].find(n => !used.includes(n)) || 'a';
}
function relSet(st, goal) {
  const s = new Set();
  const add = f => subformulas(f).forEach(g => s.add(str(g)));
  if (goal) add(goal);
  st.lines.forEach(l => { if (l.f && l.kind !== 'step') add(l.f); });
  return s;
}

/* ---------- reglas ---------- */
const one = (c, msg) => {
  if (c.L.length !== 1) fail(msg || 'Selecciona exactamente una línea.');
  return c.L[0];
};
const two = (c, msg) => { if (c.L.length !== 2) fail(msg); return c.L; };
function hypSub(c, i) {
  const s = c.subs[i || 0];
  if (!s.last) fail('La subprueba debe terminar en una línea propia, no en otra subprueba.');
  return s;
}
const NOSUB = 'Esta regla necesita una subprueba. Ábrela con «Suponer», trabaja dentro y pulsa la regla cuando llegues a lo que buscas.';
/* resultado de una regla: fórmula, líneas citadas, líneas de las que depende y subpruebas que descarga */
const res = (f, cites, src, dis) => ({ f, cites, src: src || [], dis: dis || [] });

/* ----- axiomas: esquemas con huecos (A, B, C…). El jugador rellena los huecos con fórmulas. -----
   slots: los huecos; cands(a, c): las instancias posibles a partir de lo escrito (varias si hay que elegir un nombre). */
const AXIOMS = {};
function axiom(id, o) {
  AXIOMS[id] = o;
  return { ax: true, noLines: true, name: o.name, desc: o.text, use: o.use || 'Pulsa el axioma y rellena los huecos con fórmulas.', syms: o.syms || '', slots: o.slots,
    fn: c => {
      if (!o.slots.length) return o.cands({}, c);
      const a = c.args;
      if (!a || o.slots.some(s => !a[s.k])) return { need: 'schema', slots: o.slots, text: o.text, id };
      return o.cands(a, c);
    } };
}
const sl = (...ks) => ks.map(k => ({ k, label: k }));
const PROP = {
  A1: ['A→(B→A)', 'Axioma del condicional I (se añade una premisa que sobra)', ['A', 'B'], '→', a => Imp(a.A, Imp(a.B, a.A))],
  A2: ['(A→(B→C))→((A→B)→(A→C))', 'Axioma del condicional II (distribución del condicional)', ['A', 'B', 'C'], '→', a => Imp(Imp(a.A, Imp(a.B, a.C)), Imp(Imp(a.A, a.B), Imp(a.A, a.C)))],
  A3: ['A→(B→(A∧B))', 'Axioma de la conjunción I (introducción)', ['A', 'B'], '∧→', a => Imp(a.A, Imp(a.B, And(a.A, a.B)))],
  A4: ['(A∧B)→A', 'Axioma de la conjunción II (primera parte)', ['A', 'B'], '∧→', a => Imp(And(a.A, a.B), a.A)],
  A5: ['(A∧B)→B', 'Axioma de la conjunción III (segunda parte)', ['A', 'B'], '∧→', a => Imp(And(a.A, a.B), a.B)],
  A6: ['A→(A∨B)', 'Axioma de la disyunción I (primer lado)', ['A', 'B'], '∨→', a => Imp(a.A, Or(a.A, a.B))],
  A7: ['B→(A∨B)', 'Axioma de la disyunción II (segundo lado)', ['A', 'B'], '∨→', a => Imp(a.B, Or(a.A, a.B))],
  A8: ['(A→C)→((B→C)→((A∨B)→C))', 'Axioma de la disyunción III (por casos)', ['A', 'B', 'C'], '∨→', a => Imp(Imp(a.A, a.C), Imp(Imp(a.B, a.C), Imp(Or(a.A, a.B), a.C)))],
  A9: ['(A→B)→((A→¬B)→¬A)', 'Axioma de la negación I (reducción al absurdo)', ['A', 'B'], '¬→', a => Imp(Imp(a.A, a.B), Imp(Imp(a.A, Not(a.B)), Not(a.A)))],
  A10: ['¬¬A→A', 'Axioma de la negación II (doble negación, solo clásico)', ['A'], '¬→', a => Imp(Not(Not(a.A)), a.A)],
  A10i: ['¬A→(A→B)', 'Axioma de la negación II intuicionista (explosión)', ['A', 'B'], '¬→', a => Imp(Not(a.A), Imp(a.A, a.B))],
  A11: ['(A↔B)→(A→B)', 'Axioma del bicondicional I', ['A', 'B'], '↔→', a => Imp(Iff(a.A, a.B), Imp(a.A, a.B))],
  A12: ['(A↔B)→(B→A)', 'Axioma del bicondicional II', ['A', 'B'], '↔→', a => Imp(Iff(a.A, a.B), Imp(a.B, a.A))],
  A13: ['(A→B)→((B→A)→(A↔B))', 'Axioma del bicondicional III', ['A', 'B'], '↔→', a => Imp(Imp(a.A, a.B), Imp(Imp(a.B, a.A), Iff(a.A, a.B)))],
  LEM: ['A∨¬A', 'Tercero excluido (axioma de LP)', ['A'], '∨¬', a => Or(a.A, Not(a.A))],
  K: ['□(A→B)→(□A→□B)', 'Axioma K (la caja se reparte sobre el condicional)', ['A', 'B'], '□→', a => Imp(Box(Imp(a.A, a.B)), Imp(Box(a.A), Box(a.B)))],
  T: ['□A→A', 'Axioma T (lo necesario es verdadero)', ['A'], '□→', a => Imp(Box(a.A), a.A)],
  '4': ['□A→□□A', 'Axioma 4 (lo necesario es necesariamente necesario)', ['A'], '□→', a => Imp(Box(a.A), Box(Box(a.A)))],
  '5': ['¬□A→□¬□A', 'Axioma 5 (lo que no es necesario, es necesariamente no necesario)', ['A'], '¬□→', a => Imp(Not(Box(a.A)), Box(Not(Box(a.A))))]
};
const RULES = {};
Object.keys(PROP).forEach(id => {
  const [text, name, slots, syms, make] = PROP[id];
  RULES[id] = axiom(id, { text, name, slots: sl(...slots), syms, cands: a => [res(make(a), '')] });
});
RULES.A14 = axiom('A14', { text: '¬⊥', name: 'Axioma del absurdo: ¬⊥', use: 'Pulsa el axioma: no tiene huecos.', slots: [], syms: '¬⊥', cands: () => [res(Not(Bot), '')] });

/* axiomas de los cuantificadores: el jugador escribe una fórmula entera y el juego construye la instancia */
const quant = (f, q, msg) => { if (f.t !== q) fail(msg); return f; };
RULES.Q1 = axiom('Q1', { text: '∀xA(x)→A(c)', name: 'Axioma Q1 (particularización)', syms: '∀→', use: 'Escribe ∀xA(x) y elige el nombre c.',
  slots: [{ k: 'A', label: '∀xA(x)' }],
  cands: (a, c) => {
    const f = quant(a.A, 'all', 'Escribe una fórmula que empiece por ∀.');
    const ts = namesInPlay(c.st, c.goal);
    ts.push(freshName(c.st, c.goal));
    return ts.map(t => res(Imp(f, subst(f.a, f.v, t)), ''));
  } });
RULES.Q2 = axiom('Q2', { text: 'A(c)→∃xA(x)', name: 'Axioma Q2 (generalización existencial)', syms: '∃→', use: 'Escribe A(c), con el nombre c, y elige qué apariciones pasan a variable.',
  slots: [{ k: 'A', label: 'A(c)' }],
  cands: (a, c) => {
    const f = a.A, ns = [...names(f)];
    if (!ns.length) fail('A(c) tiene que mencionar un nombre (a, b, c…) que pase a ser la variable.');
    const used = varsOf(f), out = [];
    for (const v of [...VARS].filter(x => !used.has(x)).slice(0, 3))
      for (const n of ns) {
        const k = countName(f, n), full = (1 << k) - 1;
        const masks = [full];
        if (k <= 3) for (let m = full - 1; m >= 1; m--) masks.push(m);
        masks.forEach(m => out.push(res(Imp(f, Qf('ex', v, replName(f, n, v, m))), '')));
      }
    return out;
  } });
RULES.Q3 = axiom('Q3', { text: '∀x(A→B)→(A→∀xB)', name: 'Axioma Q3 (el cuantificador cruza el condicional)', syms: '∀→', use: 'Escribe ∀x(A→B), con x libre solo en B.',
  slots: [{ k: 'A', label: '∀x(A→B)' }],
  cands: a => {
    const f = quant(a.A, 'all', 'Escribe una fórmula de la forma ∀x(A→B).');
    if (f.a.t !== 'imp') fail('Después de ∀x tiene que venir un condicional A→B.');
    if (freeVars(f.a.a).has(f.v)) fail('En Q3 la variable ' + f.v + ' no puede estar libre en A.');
    return [res(Imp(f, Imp(f.a.a, Qf('all', f.v, f.a.b))), '')];
  } });
RULES.Q4 = axiom('Q4', { text: '∀x(A→B)→(∃xA→B)', name: 'Axioma Q4 (el existencial como antecedente)', syms: '∀∃→', use: 'Escribe ∀x(A→B), con x libre solo en A.',
  slots: [{ k: 'A', label: '∀x(A→B)' }],
  cands: a => {
    const f = quant(a.A, 'all', 'Escribe una fórmula de la forma ∀x(A→B).');
    if (f.a.t !== 'imp') fail('Después de ∀x tiene que venir un condicional A→B.');
    if (freeVars(f.a.b).has(f.v)) fail('En Q4 la variable ' + f.v + ' no puede estar libre en B.');
    return [res(Imp(f, Imp(Qf('ex', f.v, f.a.a), f.a.b)), '')];
  } });
RULES.BF = axiom('BF', { text: '∀x□A(x)→□∀xA(x)', name: 'Axioma de Barcan', syms: '∀□→', use: 'Escribe ∀x□A(x).',
  slots: [{ k: 'A', label: '∀x□A(x)' }],
  cands: a => {
    const f = quant(a.A, 'all', 'Escribe una fórmula que empiece por ∀.');
    if (f.a.t !== 'box') fail('Después de ∀x tiene que venir □.');
    return [res(Imp(f, Box(Qf('all', f.v, f.a.a))), '')];
  } });

const ruleRows = {
  'R': {
    name: 'Reiteración', desc: 'Repite una línea disponible.', use: 'Selecciona 1 línea.',
    fn: c => { const l = one(c, 'Selecciona la línea que quieres repetir.'); return [res(l.f, '' + l.n, [l.n])]; }
  },
  'MP': {
    name: 'Modus ponens (la regla de Hilbert)', desc: 'De A→B y A, concluye B.', use: 'Selecciona 2 líneas.',
    fn: c => {
      const [x, y] = two(c, 'Selecciona dos líneas: un condicional A→B y su antecedente A.');
      const out = [];
      for (const [p, q] of [[x, y], [y, x]])
        if (p.f.t === 'imp' && eq(p.f.a, q.f)) out.push(res(p.f.b, p.n + ', ' + q.n, [p.n, q.n]));
      if (!out.length) {
        if (x.f.t !== 'imp' && y.f.t !== 'imp') fail('Ninguna de las dos líneas es un condicional A→B.');
        fail('La otra línea tiene que ser exactamente el antecedente del condicional.');
      }
      return out;
    }
  },
  'TD': { noLines: true,
    name: 'Teorema de la deducción', desc: 'Si de la hipótesis A (más lo que ya tenías) se llega a B, concluye A→B.',
    use: 'Pulsa la regla dentro de la subprueba.', subs: 1,
    fn: c => { const s = hypSub(c); return [res(Imp(s.hyp, s.last), s.ref, [], [s])]; }
  },
  'Nec': {
    name: 'Regla de necesitación', desc: 'De un teorema A (una línea que no depende de premisas ni supuestos), concluye □A.', use: 'Selecciona 1 línea sin dependencias.',
    fn: c => {
      const l = one(c, 'Selecciona la línea de la que quieres hacer □.');
      if (l.deps.length) fail('La línea ' + l.n + ' depende de ' + (c.st.lines[l.deps[0]].kind === 'prem' ? 'una premisa' : 'un supuesto') + ' (línea ' + (l.deps[0] + 1) + '). La necesitación solo vale para teoremas: líneas que se prueban sin premisas ni supuestos abiertos.');
      return [res(Box(l.f), '' + l.n, [l.n])];
    }
  },
  'Gen': {
    name: 'Regla de generalización', desc: 'De A(c), concluye ∀xA(x), si c no aparece en premisas ni en supuestos abiertos.', use: 'Selecciona 1 línea.',
    syms: '∀',
    fn: c => {
      const l = one(c, 'Selecciona la línea que quieres generalizar.');
      const ns = [...names(l.f)];
      if (!ns.length) fail('La línea ' + l.n + ' no menciona ningún nombre sobre el que generalizar.');
      const blocked = new Set();
      c.hyps.forEach(h => names(h, blocked));
      const ok = ns.filter(n => !blocked.has(n));
      if (!ok.length) fail('No puedes generalizar sobre «' + ns.join(', ') + '»: aparece en una premisa o en un supuesto abierto, así que no es un individuo arbitrario.');
      const used = varsOf(l.f), out = [];
      for (const v of [...VARS].filter(x => !used.has(x)).slice(0, 3))
        for (const n of ok) out.push(res(Qf('all', v, replName(l.f, n, v, -1)), '' + l.n, [l.n]));
      return out;
    }
  },
  'RK': {
    name: 'Regla K', desc: 'De □(A→B) y □A, concluye □B.', use: 'Selecciona 2 líneas.', syms: '□',
    fn: c => {
      const [x, y] = two(c, 'Selecciona dos líneas: □(A→B) y □A.');
      const out = [];
      for (const [p, q] of [[x, y], [y, x]])
        if (p.f.t === 'box' && p.f.a.t === 'imp' && q.f.t === 'box' && eq(p.f.a.a, q.f.a)) out.push(res(Box(p.f.a.b), p.n + ', ' + q.n, [p.n, q.n]));
      if (!out.length) fail('Necesitas □(A→B) y □A con la misma A.');
      return out;
    }
  },
  '∧I': {
    name: 'Introducción de la conjunción', desc: 'De A y de B, concluye A∧B.', use: 'Selecciona 2 líneas.',
    fn: c => {
      if (c.L.length < 1 || c.L.length > 2) fail('Selecciona las dos líneas que quieres unir con ∧.');
      const a = c.L[0], b = c.L[1] || a;
      return [res(And(a.f, b.f), a.n + ', ' + b.n, [a.n, b.n]), res(And(b.f, a.f), b.n + ', ' + a.n, [a.n, b.n])];
    }
  },
  '∧E': {
    name: 'Eliminación de la conjunción', desc: 'De A∧B, concluye A (o B).', use: 'Selecciona 1 línea con una conjunción.',
    fn: c => {
      const l = one(c, 'Selecciona una línea con una conjunción A∧B.');
      if (l.f.t !== 'and') fail('La línea ' + l.n + ' no es una conjunción: su conectiva principal no es ∧.');
      return [res(l.f.a, '' + l.n, [l.n]), res(l.f.b, '' + l.n, [l.n])];
    }
  },
  '∨I': {
    name: 'Introducción de la disyunción', desc: 'De A, concluye A∨B (o B∨A) para cualquier B.', use: 'Selecciona 1 línea y elige la otra fórmula.',
    fn: c => {
      const l = one(c, 'Selecciona la línea que será uno de los lados de la disyunción.');
      if (!c.P) return { need: '¿Qué fórmula pones al otro lado de ∨?', kind: 'or' };
      return [res(Or(l.f, c.P), '' + l.n, [l.n]), res(Or(c.P, l.f), '' + l.n, [l.n])];
    }
  },
  '∨E': {
    name: 'Eliminación de la disyunción', desc: 'De A∨B, una subprueba de A a C y otra de B a C, concluye C.',
    use: 'Haz una subprueba por caso y pulsa la regla.', subs: 2,
    noSub: 'Para ∨E necesitas dos subpruebas: una que suponga el primer lado de la disyunción y otra que suponga el segundo, y las dos deben llegar a la misma fórmula.',
    fn: c => {
      if (c.L.length > 1) fail('Selecciona solo la línea con la disyunción; las dos subpruebas se detectan solas.');
      if (c.L.length === 1 && c.L[0].f.t !== 'or') fail('La línea ' + c.L[0].n + ' no es una disyunción A∨B.');
      const ds = c.L.length ? c.L : c.avail().filter(l => l.f.t === 'or');
      if (!ds.length) fail('No hay ninguna disyunción A∨B disponible para razonar por casos.');
      const out = [];
      for (const d of ds) for (const s1 of c.subs) for (const s2 of c.subs) {
        if (s1 === s2 || !s1.last || !s2.last) continue;
        if (c.close && !s1.open && !s2.open) continue;
        if (eq(s1.hyp, d.f.a) && eq(s2.hyp, d.f.b) && eq(s1.last, s2.last))
          out.push(res(s1.last, d.n + ', ' + s1.ref + ', ' + s2.ref, [d.n], [s1, s2]));
      }
      if (!out.length) fail(ruleRows['∨E'].noSub);
      return out;
    }
  },
  '¬I': { noLines: true,
    name: 'Introducción de la negación', desc: 'De una subprueba que supone A y llega a ⊥, concluye ¬A.',
    use: 'Pulsa la regla cuando la subprueba llegue a ⊥.', subs: 1,
    fn: c => {
      const s = hypSub(c);
      if (s.last.t !== 'bot') fail('Para ¬I la subprueba debe terminar en ⊥. Busca una fórmula y su negación y aplica ¬E.');
      return [res(Not(s.hyp), s.ref, [], [s])];
    }
  },
  '¬E': {
    name: 'Eliminación de la negación', desc: 'De A y ¬A, concluye ⊥.', use: 'Selecciona 2 líneas.',
    fn: c => {
      const [x, y] = two(c, 'Selecciona dos líneas: una fórmula A y su negación ¬A.');
      for (const [p, q] of [[x, y], [y, x]])
        if (q.f.t === 'not' && eq(q.f.a, p.f)) return [res(Bot, p.n + ', ' + q.n, [p.n, q.n])];
      fail('Esas dos líneas no se contradicen: una debe ser exactamente la negación de la otra.');
    }
  },
  '⊥E': {
    name: 'Ex falso quodlibet', desc: 'De ⊥, concluye cualquier fórmula.', use: 'Selecciona la línea con ⊥ y elige la fórmula.',
    fn: c => {
      const l = one(c, 'Selecciona la línea con ⊥.');
      if (l.f.t !== 'bot') fail('La línea ' + l.n + ' no es ⊥.');
      if (!c.P) return { need: '¿Qué fórmula quieres obtener del absurdo?', kind: 'bot' };
      return [res(c.P, '' + l.n, [l.n])];
    }
  },
  '¬¬E': {
    name: 'Eliminación de la doble negación', desc: 'De ¬¬A, concluye A.', use: 'Selecciona 1 línea.',
    fn: c => {
      const l = one(c, 'Selecciona una línea de la forma ¬¬A.');
      if (l.f.t !== 'not' || l.f.a.t !== 'not') fail('La línea ' + l.n + ' no empieza por dos negaciones.');
      return [res(l.f.a.a, '' + l.n, [l.n])];
    }
  },
  '↔I': { noLines: true,
    name: 'Introducción del bicondicional', desc: 'De una subprueba de A a B y otra de B a A, concluye A↔B.',
    use: 'Haz las dos subpruebas y pulsa la regla.', subs: 2,
    noSub: 'Para ↔I necesitas dos subpruebas: una que suponga A y llegue a B, y otra que suponga B y llegue a A.',
    fn: c => {
      const out = [];
      for (const s1 of c.subs) for (const s2 of c.subs) {
        if (s1 === s2 || !s1.last || !s2.last) continue;
        if (c.close && !s1.open && !s2.open) continue;
        if (eq(s1.hyp, s2.last) && eq(s2.hyp, s1.last)) out.push(res(Iff(s1.hyp, s2.hyp), s1.ref + ', ' + s2.ref, [], [s1, s2]));
      }
      if (!out.length) fail(ruleRows['↔I'].noSub);
      return out;
    }
  },
  '↔E': {
    name: 'Eliminación del bicondicional', desc: 'De A↔B y uno de sus lados, concluye el otro.', use: 'Selecciona 2 líneas.',
    fn: c => {
      const [x, y] = two(c, 'Selecciona dos líneas: un bicondicional A↔B y uno de sus lados.');
      const out = [];
      for (const [p, q] of [[x, y], [y, x]]) if (p.f.t === 'iff') {
        if (eq(p.f.a, q.f)) out.push(res(p.f.b, p.n + ', ' + q.n, [p.n, q.n]));
        if (eq(p.f.b, q.f)) out.push(res(p.f.a, p.n + ', ' + q.n, [p.n, q.n]));
      }
      if (!out.length) fail('Necesitas un bicondicional A↔B y una línea que sea exactamente uno de sus lados.');
      return out;
    }
  },
  '∀E': {
    name: 'Eliminación del universal', desc: 'De ∀xA(x), concluye A(c) para el nombre c que quieras.', use: 'Selecciona 1 línea y elige el nombre.',
    fn: c => {
      const l = one(c, 'Selecciona una línea que empiece por ∀.');
      if (l.f.t !== 'all') fail('La línea ' + l.n + ' no es un universal: su símbolo principal no es ∀.');
      const ts = namesInPlay(c.st, c.goal);
      ts.push(freshName(c.st, c.goal));
      return ts.map(t => res(subst(l.f.a, l.f.v, t), '' + l.n, [l.n]));
    }
  },
  '∃I': {
    name: 'Introducción del existencial', desc: 'De A(c), concluye ∃xA(x).', use: 'Selecciona 1 línea.',
    fn: c => {
      const l = one(c, 'Selecciona la línea que da el ejemplo.');
      const ns = [...names(l.f)];
      if (!ns.length) fail('La línea ' + l.n + ' no menciona a ningún individuo (a, b, c…) que sirva de ejemplo.');
      const used = varsOf(l.f), out = [];
      for (const v of [...VARS].filter(x => !used.has(x)).slice(0, 3))
        for (const n of ns) {
          const k = countName(l.f, n), full = (1 << k) - 1;
          const masks = [full];
          if (k <= 3) for (let m = full - 1; m >= 1; m--) masks.push(m);
          masks.forEach(m => out.push(res(Qf('ex', v, replName(l.f, n, v, m)), '' + l.n, [l.n])));
        }
      return out;
    }
  },
  '∃E': {
    name: 'Eliminación del existencial', desc: 'De ∃xA(x) y una subprueba que supone A(c), con c nuevo, y llega a B sin c, concluye B.',
    use: 'Supón la instancia con un nombre nuevo y pulsa la regla al final.', subs: 1,
    fn: c => {
      const s = hypSub(c);
      if (c.L.length > 1) fail('Selecciona solo la línea con el existencial.');
      if (c.L.length === 1 && c.L[0].f.t !== 'ex') fail('La línea ' + c.L[0].n + ' no es un existencial: su símbolo principal no es ∃.');
      const es = c.L.length ? c.L : c.avail().filter(l => l.f.t === 'ex');
      if (!es.length) fail('No hay ningún existencial ∃x… disponible.');
      const out = [];
      let why = null;
      for (const e of es) {
        const n = instName(e.f, s.hyp);
        if (n === false) { why = why || 'El supuesto de la subprueba debe ser una instancia del existencial: la misma fórmula con un nombre nuevo en lugar de la variable.'; continue; }
        if (n) {
          if (names(e.f).has(n)) { why = 'El nombre «' + n + '» ya aparece en el existencial. Usa un nombre nuevo.'; continue; }
          if (names(s.last).has(n)) { why = 'La última línea de la subprueba todavía menciona a «' + n + '». Tiene que valer sin depender de ese nombre.'; continue; }
          if (c.hyps.some(h => names(h).has(n))) { why = 'El nombre «' + n + '» no es nuevo: aparece en una premisa o en un supuesto abierto.'; continue; }
        }
        out.push(res(s.last, e.n + ', ' + s.ref, [e.n], [s]));
      }
      if (!out.length) fail(why);
      return out;
    }
  },
  'Def◇': {
    name: 'Definición de la posibilidad', desc: '◇A es una abreviatura de ¬□¬A: se puede cambiar una por otra, en cualquier lugar de la fórmula.', use: 'Selecciona 1 línea y elige qué cambio hacer.', syms: '◇',
    fn: c => {
      const l = one(c, 'Selecciona una línea que tenga ◇A o ¬□¬A.'), out = [];
      const go = (g, wrap) => {
        if (g.t === 'dia') out.push(wrap(Not(Box(Not(g.a)))));
        if (g.t === 'not' && g.a.t === 'box' && g.a.a.t === 'not') out.push(wrap(Dia(g.a.a.a)));
        if (g.a) go(g.a, x => wrap(Object.assign({}, g, { a: x })));
        if (g.b) go(g.b, x => wrap(Object.assign({}, g, { b: x })));
      };
      go(l.f, x => x);
      if (!out.length) fail('Def◇ se aplica a una fórmula que contenga ◇A o ¬□¬A.');
      return out.map(g => res(g, '' + l.n, [l.n]));
    }
  },
  'Mon': {
    name: 'Monotonía', desc: 'De un teorema A→B (sin dependencias) y □A, concluye □B.', use: 'Selecciona 2 líneas.', syms: '□',
    fn: c => {
      const [x, y] = two(c, 'Selecciona dos líneas: un teorema A→B y □A.');
      const out = [];
      let why = null;
      for (const [p, q] of [[x, y], [y, x]])
        if (p.f.t === 'imp' && q.f.t === 'box' && eq(p.f.a, q.f.a)) {
          if (p.deps.length) { why = 'La línea ' + p.n + ' depende de una premisa o de un supuesto: no es un teorema. Cierra primero los supuestos con TD.'; continue; }
          out.push(res(Box(p.f.b), p.n + ', ' + q.n, [p.n, q.n]));
        }
      if (!out.length) fail(why || 'Necesitas un teorema A→B y una línea □A con la misma A.');
      return out;
    }
  },
  'DN': {
    name: 'Doble negación', desc: 'A y ¬¬A son intercambiables.', use: 'Selecciona 1 línea.',
    fn: c => {
      const l = one(c, 'Selecciona una línea.'), out = [];
      if (l.f.t === 'not' && l.f.a.t === 'not') out.push(res(l.f.a.a, '' + l.n, [l.n]));
      out.push(res(Not(Not(l.f)), '' + l.n, [l.n]));
      return out;
    }
  },
  'DeM': {
    name: 'Leyes de De Morgan', desc: '¬(A∧B) equivale a ¬A∨¬B; ¬(A∨B) equivale a ¬A∧¬B.', use: 'Selecciona 1 línea.',
    fn: c => {
      const l = one(c, 'Selecciona una línea.'), f = l.f, out = [];
      if (f.t === 'not' && f.a.t === 'and') out.push(Or(Not(f.a.a), Not(f.a.b)));
      if (f.t === 'not' && f.a.t === 'or') out.push(And(Not(f.a.a), Not(f.a.b)));
      if (f.t === 'or' && f.a.t === 'not' && f.b.t === 'not') out.push(Not(And(f.a.a, f.b.a)));
      if (f.t === 'and' && f.a.t === 'not' && f.b.t === 'not') out.push(Not(Or(f.a.a, f.b.a)));
      if (!out.length) fail('DeM se aplica a ¬(A∧B), ¬(A∨B), ¬A∨¬B o ¬A∧¬B.');
      return out.map(g => res(g, '' + l.n, [l.n]));
    }
  },
  'QN': {
    name: 'Negación de cuantificadores', desc: '¬∀xA equivale a ∃x¬A; ¬∃xA equivale a ∀x¬A.', use: 'Selecciona 1 línea.',
    fn: c => {
      const l = one(c, 'Selecciona una línea.'), f = l.f, out = [];
      if (f.t === 'not' && f.a.t === 'all') out.push(Qf('ex', f.a.v, Not(f.a.a)));
      if (f.t === 'not' && f.a.t === 'ex') out.push(Qf('all', f.a.v, Not(f.a.a)));
      if (f.t === 'ex' && f.a.t === 'not') out.push(Not(Qf('all', f.v, f.a.a)));
      if (f.t === 'all' && f.a.t === 'not') out.push(Not(Qf('ex', f.v, f.a.a)));
      if (!out.length) fail('QN se aplica a ¬∀xA, ¬∃xA, ∃x¬A o ∀x¬A.');
      return out.map(g => res(g, '' + l.n, [l.n]));
    }
  }
};
Object.assign(RULES, ruleRows);
const ORDER = ['A1', 'A2', 'A3', 'A4', 'A5', 'A6', 'A7', 'A8', 'A9', 'A10', 'A10i', 'A11', 'A12', 'A13', 'A14', 'LEM', 'Q1', 'Q2', 'Q3', 'Q4', 'K', 'T', '4', '5', 'BF',
  'R', 'MP', 'TD', 'Nec', 'Gen', 'RK', 'Mon', '∧I', '∧E', '∨I', '∨E', '¬I', '¬E', '⊥E', '¬¬E', '↔I', '↔E', '∀E', '∃I', '∃E', 'Def◇', 'DN', 'DeM', 'QN'];

/* Aplica una regla. sel: nº de línea (>0) o -nº de la primera línea de una subprueba cerrada.
   Devuelve {ok, st} | {error} | {need:'formula', prompt, kind, A} | {need:'schema', slots, text} | {need:'choice', options}. */
function apply(st, rid, sel, extra, goal) {
  extra = extra || {};
  const rule = RULES[rid];
  const selL = rule.noLines ? [] : sel.filter(x => x > 0);
  const selS = sel.filter(x => x < 0).map(x => subAt(st, -x)).filter(Boolean);
  const nS = rule.subs || 0;
  const attempts = [];
  if (!nS) attempts.push({ base: st.open, close: false, pool: [] });
  else {
    const closedAcc = base => Object.values(st.subs)
      .filter(sp => sp.end != null && subK(st, sp, base) === 0).sort((a, b) => b.start - a.start);
    if (selS.length >= nS) attempts.push({ base: st.open, close: false, pool: selS });
    else {
      if (st.open.length) {
        const base = st.open.slice(0, -1);
        const openSp = st.subs[st.open[st.open.length - 1]];
        attempts.push({ base, close: true, pool: [openSp, ...selS, ...(nS > 1 && !selS.length ? closedAcc(base) : [])] });
      }
      const ca = closedAcc(st.open);
      const rest = nS === 1 ? ca.filter(sp => sp.end === st.lines.length - 1) : ca;
      attempts.push({ base: st.open, close: false, pool: selS.length ? [...selS, ...(nS > 1 ? ca.filter(s => !selS.includes(s)) : [])] : rest });
    }
  }
  const rel = relSet(st, goal);
  let firstErr = null;
  for (const at of attempts) {
    try {
      const L = selL.map(n => {
        const k = lineK(st, n - 1, at.base);
        if (k < 0) fail('La línea ' + n + ' no se puede citar desde ahí: queda dentro de una subprueba cerrada.');
        return { n, f: st.lines[n - 1].f, deps: st.lines[n - 1].deps };
      });
      at.pool.forEach(sp => { if (sp.end != null && subK(st, sp, at.base) !== 0) fail('Esa subprueba no se puede citar desde aquí.'); });
      if (at.pool.length < nS) fail(rule.noSub || NOSUB);
      const ctx = {
        st, goal, L, close: at.close, P: extra.f || null, args: extra.args || null,
        subs: at.pool.map(sp => subInfo(st, sp)),
        hyps: openHyps(st, at.base),
        avail: () => st.lines.map((l, i) => ({ n: i + 1, f: l.f, k: lineK(st, i, at.base) })).filter(l => l.k === 0)
      };
      const out = rule.fn(ctx);
      if (out.need === 'schema') return { need: 'schema', slots: out.slots, text: out.text, id: out.id };
      if (out.need) return { need: 'formula', prompt: out.need, kind: out.kind, A: L[0] ? L[0].f : null };
      const seen = new Set();
      let cands = out.filter(c => { const k = str(c.f); if (seen.has(k)) return false; seen.add(k); return true; });
      cands.sort((a, b) => (rel.has(str(b.f)) ? 1 : 0) - (rel.has(str(a.f)) ? 1 : 0));
      let pick = null;
      if (extra.out != null) {
        pick = cands.find(c => str(c.f) === extra.out);
        if (!pick) fail('Ese resultado no se obtiene con ' + rid + '.');
      } else if (cands.length === 1) pick = cands[0];
      else return { need: 'choice', options: cands.slice(0, 12).map(c => c.f) };
      /* dependencias: las de las líneas citadas y las de la última línea de cada subprueba, menos su supuesto */
      const deps = new Set();
      pick.src.forEach(n => st.lines[n - 1].deps.forEach(d => deps.add(d)));
      pick.dis.forEach(s => { st.lines[s.lastIdx].deps.forEach(d => deps.add(d)); deps.delete(s.hypIdx); });
      const ns = clone(st);
      if (at.close) { const id = ns.open.pop(); ns.subs[id].end = ns.lines.length - 1; }
      ns.lines.push({ f: pick.f, kind: 'step', rule: rid, cites: pick.cites, path: ns.open.slice(), deps: [...deps].sort((a, b) => a - b) });
      return { ok: true, st: ns };
    } catch (e) {
      if (!(e instanceof LErr)) throw e;
      firstErr = firstErr || e.message;
    }
  }
  return { error: firstErr };
}

/* paso de una solución: ['H', f] supuesto · ['C'] cerrar · [regla, líneas, resultado, fórmula extra, huecos] */
function step(st, s, goal) {
  const op = s[0];
  if (op === 'H') return addHyp(st, parse(s[1]));
  if (op === 'C') return closeSub(st);
  const args = s[4] ? Object.fromEntries(Object.entries(s[4]).map(([k, v]) => [k, parse(v)])) : null;
  const r = apply(st, op, s[1] || [], { out: s[2], f: s[3] ? parse(s[3]) : null, args }, goal);
  if (r.ok) return r.st;
  fail(r.error || 'Paso ambiguo (' + op + '): falta ' + (r.need === 'choice' ? 'elegir el resultado' : r.need));
}

/* sugerencias para los cuadros de fórmula */
function suggest(kind, st, goal, A) {
  const out = [], seen = new Set();
  const push = f => { const k = str(f); if (closed(f) && !seen.has(k)) { seen.add(k); out.push(f); } };
  const acc = st.lines.filter((l, i) => lineK(st, i, st.open) === 0).map(l => l.f);
  const all = [];
  if (goal) subformulas(goal, all);
  st.lines.forEach(l => { if (l.f) subformulas(l.f, all); });
  const bySize = all.slice().sort((a, b) => size(a) - size(b));
  if (kind === 'hyp') {
    const fr = freshName(st, goal);
    acc.forEach(f => { if (f.t === 'ex') push(subst(f.a, f.v, fr)); });
    acc.forEach(f => { if (f.t === 'or') { push(f.a); push(f.b); } });
    all.forEach(g => { if (g.t === 'imp') push(g.a); });
    all.forEach(g => { if (g.t === 'not') push(g.a); });
    if (goal && goal.t !== 'bot') push(Not(goal));
    all.forEach(g => { if (g.t === 'iff') { push(g.a); push(g.b); } });
    bySize.forEach(g => { if (g.t !== 'bot') push(g); });
    return out.slice(0, 10);
  }
  if (kind === 'or') {
    all.forEach(g => { if (g.t === 'or') { if (eq(g.a, A)) push(g.b); if (eq(g.b, A)) push(g.a); } });
    bySize.forEach(g => { if (g.t !== 'bot') push(g); });
    return out.slice(0, 8);
  }
  if (kind === 'slot') {   // huecos de un axioma: las fórmulas que ya están en juego, de menor a mayor
    bySize.forEach(g => push(g));
    return out.slice(0, 12);
  }
  if (kind === 'bot' && goal) push(goal);
  bySize.forEach(g => { if (g.t !== 'bot') push(g); });
  return out.slice(0, 8);
}

root.Logic = {
  VARS, NAMES, LErr, RULES, ORDER, AXIOMS,
  parse, str, eq, closed, subformulas, names, freeVars, evalF, atomsOf, groundAtoms,
  newProof, addHyp, closeSub, lineK, subK, subAt, pickSub,
  apply, step, suggest, namesInPlay, freshName, subst,
  Atom, Bot, Not, And, Or, Imp, Iff, Box, Dia, Qf
};
})(typeof window !== 'undefined' ? window : globalThis);
