/* Lógica Axiomática: verifica que cada reto tiene derivación con sus reglas, que los axiomas son válidos en su semántica y que el motor rechaza pasos inválidos. */
require('./src/engine.js');
require('./src/content.js');
require('./src/validity.js');
const VAL = globalThis.Validity;
const L = globalThis.Logic;
const C = globalThis.CONTENT;
let bad = 0, nP = 0, nM = 0, nT = 0, nG = 0, nV = 0, nX = 0;
const err = m => { bad++; console.log('  ✗ ' + m); };

C.worlds.forEach((W, wi) => W.stages.forEach((s, si) => {
  const id = W.k + '-' + (si + 1) + ' ' + s.title;
  if (!['T', 'P', 'M', 'Q', 'TT', 'GN', 'V'].includes(s.t)) err(id + ': tipo desconocido');
  if (s.t === 'P') {
    nP++;
    const rules = C.RS[s.rules];
    if (!rules) return err(id + ': conjunto de reglas desconocido');
    const goal = L.parse(s.goal);
    if (L.str(goal) !== s.goal) err(id + ': meta no canónica ' + L.str(goal));
    let st = L.newProof(s.prem.map(L.parse));
    try {
      s.sol.forEach((stp, k) => {
        if (!'HC'.includes(stp[0]) && !rules.includes(stp[0])) throw new Error('regla no permitida ' + stp[0]);
        st = L.step(st, stp, goal);
        if (stp[2] && L.str(st.lines[st.lines.length - 1].f) !== stp[2]) throw new Error('paso ' + (k + 1) + ' dio ' + L.str(st.lines[st.lines.length - 1].f));
      });
      const last = st.lines[st.lines.length - 1];
      if (last.path.length || !L.eq(last.f, goal)) throw new Error('no llega a la meta; última: ' + L.str(last.f) + ' prof. ' + last.path.length);
      if (s.hints.length < 2) throw new Error('pocas pistas');
    } catch (e) { err(id + ': ' + e.message); }
  }
  if (s.t === 'M') {
    nM++;
    const sat = s.mode === 'sat';   // en modo consistencia basta con que todas puedan ser verdaderas
    const prem = s.prem.map(L.parse), goal = sat ? L.parse('P∧¬P') : L.parse(s.goal);
    const atoms = s.dom ? L.groundAtoms([...prem, goal], s.dom) : L.atomsOf(sat ? prem : [...prem, goal]);
    const vals = s.logic === 'LP' ? [1, 0.5, 0] : [1, 0], des = v => (s.logic === 'LP' ? v >= 0.5 : v === 1);
    let found = false;
    const rec = (i, v) => {
      if (i === atoms.length) { if (prem.every(p => des(L.evalF(p, v, s.dom))) && !des(L.evalF(goal, v, s.dom))) found = true; return; }
      vals.forEach(x => rec(i + 1, Object.assign({}, v, { [atoms[i]]: x })));
    };
    rec(0, {});
    if (!found) err(id + ': no hay contraejemplo');
  }
  if (s.t === 'TT') {
    nT++;
    const cols = s.cols.map(L.parse);
    cols.forEach((f, i) => { if (L.str(f) !== s.cols[i]) err(id + ': columna no canónica'); });
    if (L.atomsOf(cols).length > 3 || !s.intro || !s.outro) err(id + ': tabla mal definida');
  }
  if (s.t === 'GN') {
    nG++;
    const codes = new Map(C.GODEL);
    if (!['enc', 'dec'].includes(s.mode) || !s.word.length || s.word.length > 5 || s.word.some(x => !codes.has(x)) || !s.intro || !s.outro) err(id + ': reto de numeración mal definido');
  }
  if (s.t === 'V') {
    nV++;
    if (si !== W.stages.length - 1) err(id + ': el motor debe ser la última etapa del mundo');
    if (!['cl', 'lp', 'modal', 'int'].includes(s.logic) || !s.intro || !s.outro || !s.ex || !s.goals) return err(id + ': motor mal definido');
    if (s.logic === 'modal' && !(s.sys && s.sys.length > 1)) err(id + ': el motor modal necesita sistemas');
    const verd = {};
    s.ex.forEach(([p, c, want, sys]) => {
      const P = p.map(L.parse), Cc = L.parse(c), tag = id + ': ' + p.join(', ') + ' ⊢ ' + c;
      [...p, c].forEach(x => { if (L.str(L.parse(x)) !== x) err(tag + ': fórmula no canónica ' + x); });
      [...p, c].join('').replace(/[A-Za-z(),\s]/g, '').split('').forEach(ch => { if (!s.syms.includes(ch)) err(tag + ': símbolo ' + ch + ' fuera del teclado del motor'); });
      if (s.sys && sys && !s.sys.includes(sys)) err(tag + ': sistema ' + sys + ' no disponible');
      const r = VAL.check(s.logic, sys || (s.sys && s.sys[0]), P, Cc);
      if (r.v !== want) err(tag + ': el motor dice ' + r.v + ', se esperaba ' + want);
      if (r.v === 'invalid' && !r.model) err(tag + ': inválido sin contraejemplo');
      verd[r.v] = 1;
      if (s.sys) { const vs = s.sys.map(x => VAL.check(s.logic, x, P, Cc).v); if (vs.includes('valid') && vs.includes('invalid')) verd.split = 1; }
      if (s.cmp && r.v === 'invalid' && VAL.check(s.cmp, null, P, Cc).v === 'valid') verd.gap = 1;
    });
    /* cada misión se puede cumplir con los propios ejemplos (salvo la de escribir uno propio) */
    s.goals.forEach(g => { if (g !== 'own' && !verd[g]) err(id + ': ningún ejemplo sirve para la misión ' + g); });
  }
  if (s.t === 'Q') s.qs.forEach(q => { if (!(q.ok >= 0 && q.ok < q.opts.length) || !q.why) err(id + ': pregunta mal formada'); });
  if (s.t === 'T') s.pages.forEach(p => { if (!p.say) err(id + ': página vacía'); });
}));

/* ---------- cada ejercicio, contrastado con la semántica de su lógica ---------- */
/* con qué lógica (y sistema) se juzga cada conjunto de reglas, y qué sistema más débil debería fallar */
const LOGIC_OF = { h0: ['cl'], h1: ['cl'], cAnd: ['cl'], cOr: ['cl'], cNeg: ['cl'], cIff: ['cl'], and: ['cl'], imp: ['cl'], or: ['cl'], neg: ['cl'], cl: ['cl'],
  q0: ['cl'], fo1: ['cl'], fo2: ['cl'], fo2q: ['cl'], cEx: ['cl'], fo: ['cl'],
  k0: ['modal', 'K'], k1: ['modal', 'K'], k: ['modal', 'K'], t: ['modal', 'T'], s4: ['modal', 'S4'], s5: ['modal', 'S5'], qk: ['modal', 'K'], qt: ['modal', 'T'],
  k4: ['modal', 'K4'], i0: ['int'], int: ['int'], intfo: ['int'], lp: ['lp'], lpq: ['lp'] };
/* en la Torre, K4 es el sistema de todo el mundo (el jefe usa como premisa lo ya probado en K4), no el de cada reto */
const WEAKER = { T: 'K', S4: 'T', S5: 'S4' };
const judge = (logic, sys, prem, concl) => VAL.check(logic, sys, prem.map(L.parse), L.parse(concl)).v;
C.worlds.forEach(W => W.stages.forEach((s, si) => {
  const id = W.k + '-' + (si + 1) + ' ' + s.title;
  if (s.t === 'P') {
    const [logic, sys] = LOGIC_OF[s.rules];
    nX++;
    /* correcto: lo que se prueba con las reglas del mundo es válido en su semántica */
    const v = judge(logic, sys, s.prem, s.goal);
    if (v !== 'valid') err(id + ': la prueba existe pero el motor (' + logic + (sys ? ' ' + sys : '') + ') dice ' + v);
    if (s.sys && sys && s.sys !== sys && !(s.sys === 'LP')) err(id + ': etiqueta ' + s.sys + ' y reglas de ' + sys);
    /* ilustrativo: el ejercicio necesita de verdad su sistema modal (falla en el más débil) */
    if (sys && WEAKER[sys] && judge(logic, WEAKER[sys], s.prem, s.goal) !== 'invalid')
      err(id + ': ya vale en ' + WEAKER[sys] + ', no hace falta ' + sys);
  }
  if (s.t === 'M') {
    nX++;
    /* ilustrativo: lo que LP refuta sí es válido en la lógica clásica (se ve qué se pierde) */
    const prem = s.prem.map(L.parse);
    if (s.logic === 'LP' && s.goal && VAL.check('cl', null, prem, L.parse(s.goal)).v !== 'valid') err(id + ': en LP falla, pero tampoco vale en la clásica');
    if (s.goal) {
      const v = VAL.check(s.logic === 'LP' ? 'lp' : 'cl', null, prem, L.parse(s.goal)).v;
      if (v !== 'invalid') err(id + ': el motor no lo refuta (' + v + ')');
    } else if (VAL.check('cl', null, prem, L.parse('⊥')).v !== 'invalid') err(id + ': el conjunto no es consistente');
  }
}));
/* lo que afirman las preguntas y la teoría: [lógica, sistema, premisas, conclusión, veredicto, dónde] */
const CLAIMS = [
  ['cl', null, ['P→Q', 'Q→R'], 'P→R', 'valid', 'M0 Validez'],
  ['cl', null, ['P', 'P→Q', '¬Q'], '⊥', 'valid', 'M0 conjunto inconsistente'],
  ['cl', null, ['P→Q', '¬P'], '⊥', 'invalid', 'M0 conjunto consistente'],
  ['cl', null, ['P∨Q', '¬P', '¬Q'], '⊥', 'valid', 'M0 conjunto inconsistente'],
  ['cl', null, ['¬(P∧Q)'], '¬P∨¬Q', 'valid', 'M0 De Morgan'], ['cl', null, ['¬P∨¬Q'], '¬(P∧Q)', 'valid', 'M0 De Morgan'],
  ['cl', null, ['P→Q'], '¬Q→¬P', 'valid', 'M0 contrapuesta'], ['cl', null, ['¬Q→¬P'], 'P→Q', 'valid', 'M0 contrapuesta'],
  ['cl', null, ['∀y∃xRxy'], '∃x∀yRxy', 'invalid', 'M2 ¿Y al revés?'],
  ['modal', 'T', [], '□P→P', 'valid', 'M3 reflexividad'], ['modal', 'K', [], '□P→P', 'invalid', 'M3 reflexividad'],
  ['modal', 'K', [], '□P→◇P', 'invalid', 'M3 mundo sin salida'],
  ['modal', 'S5', ['◇□P'], '□P', 'valid', 'M3 S5'], ['modal', 'S4', ['◇□P'], '□P', 'invalid', 'M3 S5'],
  ['modal', 'K', ['□∃xFx'], '∃x□Fx', 'invalid', 'M4 de dicto y de re'], ['modal', 'S5', ['□∃xFx'], '∃x□Fx', 'invalid', 'M4 ni siquiera en S5'],
  ['int', null, [], '¬¬P→P', 'invalid', 'M5 constructivo'], ['int', null, [], '¬(P∧Q)→(¬P∨¬Q)', 'invalid', 'M5 constructivo'],
  ['int', null, [], '(¬P∨¬Q)→¬(P∧Q)', 'valid', 'M5 constructivo'], ['int', null, [], 'P∨¬P', 'invalid', 'M5 sin tercero excluido'],
  ['int', null, ['P', '¬P'], 'Q', 'valid', 'M6 examen: la intuicionista explota'], ['modal', 'S5', ['P', '¬P'], 'Q', 'valid', 'M6 examen: S5 explota'],
  ['lp', null, ['P', '¬P'], 'Q', 'invalid', 'M6 examen: LP no explota'],
  ['lp', null, [], 'P∨¬P', 'valid', 'M6 mismos teoremas'], ['lp', null, [], '((P→Q)→P)→P', 'valid', 'M6 mismos teoremas'],
  ['lp', null, ['P∨Q', '¬P'], 'Q', 'invalid', 'M6 sin silogismo disyuntivo'],
  ['int', null, [], '¬∀xFx→∃x¬Fx', 'invalid', 'M7 con testigo'], ['int', null, [], '∃x¬Fx→¬∀xFx', 'valid', 'M7 con testigo'],
  ['cl', null, [], '∃x(Fx→∀yFy)', 'valid', 'M7 propiedad de la existencia (en la clásica sí)'],
  ['lp', null, ['∃x(Fx∧¬Fx)'], '∀xGx', 'invalid', 'M8 leyes que resisten'], ['lp', null, [], '¬∃x(Fx∧¬Fx)', 'valid', 'M8 teorema de LP'],
  ['lp', null, [], '∃x(Fx∧¬Fx)', 'invalid', 'M8 no es teorema'],
  ['modal', 'GL', ['□P'], 'P', 'invalid', 'M9 RT no vale'], ['modal', 'GL', [], '□(□P→P)→□P', 'valid', 'M9 Löb'],
  ['modal', 'K4', [], '□(□P→P)→□P', 'invalid', 'M9 Löb no está en K4'], ['modal', 'GL', ['¬□⊥'], '¬□¬□⊥', 'valid', 'M9 segundo teorema']
];
CLAIMS.forEach(([logic, sys, prem, concl, want, where]) => {
  nX++;
  const v = judge(logic, sys, prem, concl);
  if (v !== want) err(where + ': ' + prem.join(', ') + ' ⊢ ' + concl + ' en ' + logic + (sys ? ' ' + sys : '') + ' da ' + v + ', se esperaba ' + want);
});
/* ∀x¬¬Fx → ¬¬∀xFx no es intuicionista, pero solo lo refutan modelos infinitos: el motor no debe declararlo válido */
if (judge('int', null, ['∀x¬¬Fx'], '¬¬∀xFx') === 'valid') err('M7: el motor da por válido el desplazamiento de la doble negación');
/* en un dominio {a, b} con Fa = A y Fb = V, ∀xFx vale A (pregunta del Mundo 8) */
if (L.evalF(L.parse('∀xFx'), { Fa: 0.5, Fb: 1 }, ['a', 'b']) !== 0.5) err('M8: ∀xFx debería valer A');

/* ---------- el motor de validez: hechos conocidos y contraste con modelos pequeños ---------- */
let seed = 12345;
const rnd = n => { seed = (seed + 0x6D2B79F5) | 0; let t = Math.imul(seed ^ (seed >>> 15), 1 | seed); t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t; return ((t ^ (t >>> 14)) >>> 0) % n; };
const rf = (d, modal) => {
  if (d === 0 || rnd(4) === 0) return L.Atom('PQR'[rnd(3)]);
  const k = rnd(modal ? 7 : 5), a = rf(d - 1, modal);
  return [L.Not(a), L.And(a, rf(d - 1, modal)), L.Or(a, rf(d - 1, modal)), L.Imp(a, rf(d - 1, modal)), L.Iff(a, rf(d - 1, modal)), L.Box(a), L.Dia(a)][k];
};
/* todo modelo de dos mundos (con valores para P, Q, R) de cada sistema: si refuta, el motor no puede decir «válido» */
const FR = { K: [0, 0], T: [1, 0], S4: [1, 1], S5: [1, 1], K4: [0, 1], GL: [0, 1] };
function small(sys) {
  const out = [];
  for (let m = 0; m < 16; m++) {
    const R = [[m & 1, m & 2], [m & 4, m & 8]].map(r => r.map(Boolean));
    if (FR[sys][0] && !(R[0][0] && R[1][1])) continue;
    if (sys === 'GL' && (R[0][0] || R[1][1] || (R[0][1] && R[1][0]))) continue;
    if (sys === 'S5' && R[0][1] !== R[1][0]) continue;
    if (FR[sys][1] && ((R[0][1] && R[1][0]) && !(R[0][0] && R[1][1]))) continue;
    for (let v = 0; v < 64; v++) out.push({ R: R.map(r => r.map((x, j) => (x ? j : -1)).filter(j => j >= 0)), W: [0, 1].map(i => ({ P: (v >> (3 * i)) & 1, Q: (v >> (3 * i + 1)) & 1, R: (v >> (3 * i + 2)) & 1 })) });
  }
  return out;
}
const SMALL = {};
['K', 'T', 'S4', 'S5', 'K4', 'GL'].forEach(sys => { SMALL[sys] = small(sys); });
for (let i = 0; i < 300; i++) {
  const p = rf(3, true), c = rf(3, true);
  ['K', 'T', 'S4', 'S5', 'K4', 'GL'].forEach(sys => {
    const r = VAL.check('modal', sys, [p], c);
    if (r.v === 'valid' && SMALL[sys].some(M => VAL.kEval(p, 0, M) && !VAL.kEval(c, 0, M))) err('motor modal ' + sys + ': ' + L.str(p) + ' ⊢ ' + L.str(c) + ' tiene contramodelo');
  });
  const q = rf(3, false), d = rf(3, false), ci = VAL.check('int', null, [q], d).v, cc = VAL.check('cl', null, [q], d).v, cl = VAL.check('lp', null, [q], d).v;
  if ((ci === 'valid' || cl === 'valid') && cc !== 'valid') err('motor: ' + L.str(q) + ' ⊢ ' + L.str(d) + ' válido en una lógica más débil que la clásica, pero no en la clásica');
}

/* pasos que el motor debe rechazar */
const rej =(name, prem, steps, rid, sel, extra) => {
  let st = L.newProof(prem.map(L.parse));
  steps.forEach(s => { st = L.step(st, s, null); });
  const r = L.apply(st, rid, sel, extra || {}, null);
  if (!r.error) err('debía rechazarse: ' + name + ' → ' + JSON.stringify(r).slice(0, 120));
};
rej('Gen sobre nombre de premisa', ['Fa'], [], 'Gen', [1]);
rej('Gen sobre nombre de supuesto abierto', [], [['H', 'Fa']], 'Gen', [1]);
rej('Nec sobre una premisa', ['P'], [], 'Nec', [1]);
rej('Nec sobre una línea que depende de un supuesto', [], [['H', 'P']], 'Nec', [1]);
rej('Nec sobre una conclusión que usa una premisa', ['P', 'P→Q'], [['MP', [2, 1]]], 'Nec', [3]);
rej('Mon con un condicional que no es teorema', ['P→Q', '□P'], [], 'Mon', [1, 2]);
rej('Mon con antecedentes distintos', [], [['H', 'P'], ['TD']], 'Mon', [2]);
rej('citar línea de subprueba cerrada', [], [['H', 'P'], ['C']], 'R', [1]);
rej('∃E con nombre en la conclusión', ['∃xFx'], [['H', 'Fa']], '∃E', [1]);
rej('∃E con nombre viejo', ['∃xFx', 'Ga'], [['H', 'Fa'], ['∃I', [3], '∃xFx']], '∃E', [1]);
rej('¬I sin ⊥', [], [['H', 'P']], '¬I', []);
rej('TD sin subprueba', ['P'], [], 'TD', []);
rej('MP con antecedente distinto', ['P→Q', 'R'], [], 'MP', [1, 2]);
rej('∨E con casos que no coinciden', ['P∨Q'], [['H', 'P'], ['C'], ['H', 'Q']], '∨E', [1]);
rej('QN sobre una fórmula sin cuantificador negado', ['Fa∧¬Fa'], [], 'QN', [1]);
rej('RK con cajas distintas', ['□(P→Q)', '□R'], [], 'RK', [1, 2]);
rej('Def◇ sin ◇ ni ¬□¬', ['□P'], [], 'Def◇', [1]);
rej('de dicto a de re: el nombre no sale de la caja', ['□∃xFx'], [['H', 'Fa']], '∃E', [1]);
/* los axiomas con condiciones sobre la variable */
const axRej = (name, id, args) => {
  try { L.step(L.newProof([]), [id, [], null, null, args], null); err('debía rechazarse el axioma: ' + name); } catch (e) { if (!(e instanceof L.LErr)) throw e; }
};
axRej('Q3 con x libre en A', 'Q3', { A: '∀x(Fx→Gx)' });
axRej('Q4 con x libre en B', 'Q4', { A: '∀x(Fx→Gx)' });
axRej('Q1 sin universal', 'Q1', { A: 'Fa' });
axRej('Q2 sin nombre', 'Q2', { A: 'P' });
axRej('BF sin caja', 'BF', { A: '∀xFx' });

/* cada axioma es válido en la lógica a la que pertenece, con instancias al azar */
{
  const AXL = { A1: 'cl', A2: 'cl', A3: 'cl', A4: 'cl', A5: 'cl', A6: 'cl', A7: 'cl', A8: 'cl', A9: 'cl', A10: 'cl', A10i: 'int', A11: 'cl', A12: 'cl', A13: 'cl', A14: 'cl', LEM: 'lp',
    K: ['modal', 'K'], T: ['modal', 'T'], '4': ['modal', 'K4'], '5': ['modal', 'S5'] };
  const WRONG = { A10: 'int', A10i: null, LEM: 'int', T: ['modal', 'K'], '4': ['modal', 'K'], '5': ['modal', 'S4'] };   // donde no deben valer
  for (const id of Object.keys(AXL)) {
    const ax = L.AXIOMS[id], ks = ax.slots.map(x => x.k);
    for (let n = 0; n < 12; n++) {
      const a = {};
      ks.forEach(k => { a[k] = rf(2, ['K', 'T', '4', '5'].includes(id)); });
      const f = ax.cands(a, {})[0].f;
      const spec = AXL[id], [lg, sy] = Array.isArray(spec) ? spec : [spec, null];
      nX++;
      const v = VAL.check(lg, sy, [], f).v;
      if (v !== 'valid') err('axioma ' + id + ' con ' + L.str(f) + ' no es válido en ' + lg + (sy ? ' ' + sy : '') + ' (' + v + ')');
    }
  }
  /* y se distinguen: el axioma no vale en la lógica más débil */
  [['A10', 'int', null, 'P'], ['T', 'modal', 'K', 'P'], ['4', 'modal', 'K', 'P'], ['5', 'modal', 'S4', 'P'], ['LEM', 'int', null, 'P']].forEach(([id, lg, sy, p]) => {
    const f = L.AXIOMS[id].cands({ A: L.parse(p), B: L.parse('Q') }, {})[0].f;
    nX++;
    if (VAL.check(lg, sy, [], f).v !== 'invalid') err('el axioma ' + id + ' no debería valer en ' + lg + (sy ? ' ' + sy : ''));
  });
  /* esquemas de los cuantificadores y la fórmula Barcan */
  const qa = (id, a, c) => L.AXIOMS[id].cands(a, c || { st: L.newProof([]), goal: null });
  const qchecks = [['Q1', { A: L.parse('∀xFx') }, 'cl'], ['Q2', { A: L.parse('Fa') }, 'cl'], ['Q2', { A: L.parse('Laa') }, 'cl'], ['Q3', { A: L.parse('∀x(P→Fx)') }, 'cl'],
    ['Q4', { A: L.parse('∀x(Fx→P)') }, 'cl'], ['BF', { A: L.parse('∀x□Fx') }, 'modal']];
  qchecks.forEach(([id, a, lg]) => qa(id, a).forEach(r => {
    nX++;
    const v = VAL.check(lg, lg === 'modal' ? 'K' : null, [], r.f).v;
    if (v !== 'valid') err('axioma ' + id + ' con ' + L.str(r.f) + ' da ' + v);
  }));
}
/* todas las reglas de cada conjunto existen */
Object.keys(C.RS).forEach(k => C.RS[k].forEach(r => { if (!L.RULES[r]) err('el conjunto ' + k + ' menciona una regla que no existe: ' + r); }));

/* música y sprite */
require('./src/music.js'); require('./src/sprite.js');
const SG = globalThis.LAudioSongs;
Object.keys(SG).forEach(id => { const s = SG[id];
  if (s.c.steps.length !== s.bars.length * 8) err('canción ' + id + ': compases mal medidos');
  s.c.lead.forEach(e => { if (e && !(e.f > 100 && e.f < 3000)) err('canción ' + id + ': nota fuera de rango'); });
  ['arp', 'bass'].forEach(k => { if (s.c[k].length !== 8) err('canción ' + id + ': patrón ' + k); }); });
globalThis.SPRITE.BASE.forEach((r, y) => { if (r.length !== 24) err('sprite fila ' + y + ' mide ' + r.length); });
['neutral', 'happy', 'sad', 'think', 'brave'].forEach(m => globalThis.SPRITE.grid(m).forEach((r, y) => { if (r.length !== 24 || r.some(c => c !== '.' && !globalThis.SPRITE.PAL[c])) err('sprite ' + m + ' fila ' + y); }));
console.log(Object.keys(SG).length + ' canciones, sprite 24×24 con 5 expresiones');
console.log(`${nP} pruebas, ${nM} modelos, ${nT} tablas, ${nG} de Gödel, ${nV} motores, ${nX} contrastes semánticos, ${C.worlds.reduce((n, w) => n + w.stages.length, 0)} etapas · ${bad ? bad + ' ERRORES' : 'todo correcto'}`);
process.exit(bad ? 1 : 0);
