/* Lógica Axiomática — interfaz */
(function () {
'use strict';
const L = window.Logic, C = window.CONTENT;
const app = document.getElementById('app');
const modal = document.getElementById('modal');
const esc = s => String(s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));

/* ---------- glifos de píxel (7 filas) ---------- */
const GLY = {
  '¬': ['......', '......', '######', '.....#', '.....#', '......', '......'],
  '∧': ['...#...', '...#...', '..#.#..', '..#.#..', '.#...#.', '.#...#.', '#.....#'],
  '∨': ['#.....#', '.#...#.', '.#...#.', '..#.#..', '..#.#..', '...#...', '...#...'],
  '→': ['.......', '....#..', '.....#.', '#######', '.....#.', '....#..', '.......'],
  '↔': ['.........', '..#...#..', '.#.....#.', '#########', '.#.....#.', '..#...#..', '.........'],
  '⊥': ['...#...', '...#...', '...#...', '...#...', '...#...', '...#...', '#######'],
  '∀': ['#.....#', '#.....#', '.#####.', '.#...#.', '..#.#..', '..#.#..', '...#...'],
  '∃': ['######', '.....#', '.....#', '..####', '.....#', '.....#', '######'],
  '□': ['#######', '#.....#', '#.....#', '#.....#', '#.....#', '#.....#', '#######'],
  '◇': ['...#...', '..#.#..', '.#...#.', '#.....#', '.#...#.', '..#.#..', '...#...'],
  '⊢': ['#.....', '#.....', '#.....', '######', '#.....', '#.....', '#.....'],
  '⊬': ['#.....#', '#....#.', '#...#..', '#######', '#.#....', '##.....', '#......'],
  '⊨': ['#.....', '#.....', '######', '#.....', '######', '#.....', '#.....'],
  '⋮': ['.#.', '...', '...', '.#.', '...', '...', '.#.'],
  star: ['...#...', '...#...', '#######', '.#####.', '..###..', '.##.##.', '.#...#.'],
  lock: ['..###..', '.#...#.', '.#...#.', '#######', '###.###', '###.###', '#######'],
  check: ['.......', '......#', '.....##', '#...##.', '##.##..', '.###...', '..#....'],
  cross: ['#.....#', '.#...#.', '..#.#..', '...#...', '..#.#..', '.#...#.', '#.....#'],
  book: ['#####..', '#...##.', '#.....#', '#.###.#', '#.....#', '#.###.#', '#######'],
  grid: ['#######', '#.#.#.#', '#######', '#.#.#.#', '#######', '#.#.#.#', '#######'],
  quiz: ['.####.', '#....#', '....#.', '...#..', '..#...', '......', '..#...'],
  note: ['...###', '...#.#', '...#..', '...#..', '.###..', '####..', '.##...'],
  spk: ['...#...', '..##.#.', '####..#', '####..#', '####..#', '..##.#.', '...#...'],
  back: ['...#', '..##', '.###', '####', '.###', '..##', '...#'],
  next: ['#...', '##..', '###.', '####', '###.', '##..', '#...'],
  down: ['.......', '.......', '#######', '.#####.', '..###..', '...#...', '.......'],
  undo: ['..#....', '.#.....', '######.', '.#....#', '..#...#', '......#', '..####.'],
  num: ['.#.#.', '.#.#.', '#####', '.#.#.', '#####', '.#.#.', '.#.#.'],
  gear: ['..#.#..', '.#####.', '##...##', '.#...#.', '##...##', '.#####.', '..#.#..'],
  loop: ['..###.#', '.#...##', '#...###', '#......', '#.....#', '.#...#.', '..###..'],
  /* símbolos de la aritmética y de la metateoría (Mundo 9) */
  '⌜': ['###.', '#...', '#...', '....', '....', '....', '....'],
  '⌝': ['.###', '...#', '...#', '....', '....', '....', '....'],
  'ℕ': ['##...#', '###..#', '####.#', '##.###', '##..##', '##...#', '##...#'],
  'ω': ['.......', '.......', '.#...#.', '#.....#', '#..#..#', '#..#..#', '.##.##.'],
  'Σ': ['######', '#.....', '.#....', '..#...', '.#....', '#.....', '######'],
  'ε': ['.....', '.....', '.###.', '#....', '.##..', '#....', '.###.'],
  '×': ['.....', '.....', '#...#', '.#.#.', '..#..', '.#.#.', '#...#'],
  '₀': ['...', '...', '...', '###', '#.#', '#.#', '###'],
  '₁': ['...', '...', '...', '.#.', '##.', '.#.', '###']
};
const OPS = '∧∨→↔⊢⊬⊨';
const gcache = {};
function glyph(ch) {
  if (gcache[ch]) return gcache[ch];
  const rows = GLY[ch], w = rows[0].length;
  let r = '';
  rows.forEach((row, y) => {
    for (let x = 0; x < w; x++) if (row[x] === '#') {
      let x2 = x;
      while (row[x2 + 1] === '#') x2++;
      r += `<rect x="${x}" y="${y}" width="${x2 - x + 1}" height="1"/>`;
      x = x2;
    }
  });
  const cls = OPS.includes(ch) ? 'g op' : 'g';
  return (gcache[ch] = `<svg class="${cls}" viewBox="0 0 ${w} 7" style="width:${(w / 7 * 0.6).toFixed(3)}em" aria-hidden="true" shape-rendering="crispEdges">${r}</svg>`);
}
const ico = glyph;
function raw(s) {
  let h = '';
  for (const ch of String(s)) h += GLY[ch] ? glyph(ch) : esc(ch);
  return h;
}
const fm = s => `<span class="fm${L.RULES[s] ? " rn" : ""}" aria-label="${esc(s)}">${raw(s)}</span>`;
const fh = f => fm(L.str(f));
const tx = s => String(s).replace(/\{([^}]*)\}/g, (m, a) => fm(a));

/* ---------- Minerva (24×24) y sus expresiones ---------- */
const SP = window.SPRITE;
const MOODS = { neutral: 'atenta', happy: 'contenta', sad: 'preocupada', think: 'pensativa', brave: 'decidida' };
function runs(rowsOf) {
  let r = '';
  rowsOf.forEach(([x0, y, s]) => {
    for (let i = 0; i < s.length; i++) {
      const c = s[i];
      if (c === '.') continue;
      let j = i;
      while (s[j + 1] === c) j++;
      r += `<rect x="${x0 + i}" y="${y}" width="${j - i + 1}" height="1" fill="${SP.PAL[c]}"/>`;
      i = j;
    }
  });
  return r;
}
const owlCache = {};
const owlRects = mood => runs(SP.grid(mood).map((row, y) => [0, y, row.join('')]));
/* la edición ilustrada trae una imagen por expresión; el parpadeo y el pico abierto son cuadros enteros que la tapan */
const HD = window.LA_OWL_HD;
const pic = (href, cls) => `<image${cls ? ` class="${cls}"` : ''} width="24" height="24" href="${href}"/>`;
function owlBody(mood) {
  if (owlCache[mood]) return owlCache[mood];
  const spark = mood === 'happy' ? `<g class="spk">${runs(SP.SPARK)}</g>` : '';
  if (HD && HD[mood]) {
    const f = HD[mood];
    return (owlCache[mood] = pic(f.base) + (f.talk ? pic(f.talk, 'bk') : '') + (f.blink ? pic(f.blink, 'blk') : '') + spark);
  }
  const blink = mood === 'happy' ? '' : `<g class="blk">${runs(SP.eyePatch('blink'))}</g>`;
  const beak = mood === 'happy' ? '' : `<g class="bk">${runs(SP.BEAK_OPEN)}</g>`;
  return (owlCache[mood] = owlRects(mood) + blink + beak + spark);
}
const owl = (px, mood) => {
  const m = MOODS[mood] ? mood : 'neutral';
  return `<svg class="owl m-${m}" width="${24 * px}" height="${24 * px}" viewBox="0 0 24 24" shape-rendering="crispEdges" role="img" aria-label="Minerva, la lechuza, ${MOODS[m]}">${owlBody(m)}</svg>`;
};
/* el ánimo de Minerva sale del propio texto: una exclamación la alegra, una pregunta la pone a pensar */
const moodOf = text => (/¡/.test(text) ? 'happy' : /\?/.test(text) ? 'think' : 'neutral');

/* ---------- partida guardada ---------- */
const KEY = 'logica-axiomatica-v1';
const save = { done: {}, mv: null, sv: null, free: false, theme: '' };   // mv y sv: volumen de música y efectos, de 0 a 5
try { Object.assign(save, JSON.parse(localStorage.getItem(KEY) || '{}')); } catch (e) { /* sin almacenamiento */ }
if (window.LA_SAVE) Object.assign(save, window.LA_SAVE);   // partida prefijada (video promocional)
const persist = () => { try { localStorage.setItem(KEY, JSON.stringify(save)); } catch (e) { /* sin almacenamiento */ } };
if (save.mv == null) save.mv = save.music === false ? 0 : 3;
if (save.sv == null) save.sv = save.mute ? 0 : 4;
if (!save.v) {   // la versión 2 añadió el mundo 0: las claves de progreso se corren un mundo
  const d = {};
  Object.keys(save.done).forEach(k => { const p = k.split('-'); d[(+p[0] + 1) + '-' + p[1]] = save.done[k]; });
  save.done = d; save.v = 2; persist();
}
const applyTheme = () => { if (save.theme) document.documentElement.dataset.theme = save.theme; else delete document.documentElement.dataset.theme; };
applyTheme();

const sid = (w, s) => w + '-' + s;
const isEx = s => s.t !== 'T';
function wstat(w) {
  const st = C.worlds[w].stages;
  let done = 0, stars = 0;
  st.forEach((s, i) => { const d = save.done[sid(w, i)]; if (d) { done++; if (isEx(s)) stars += d; } });
  return { done, total: st.length, stars, max: st.filter(isEx).length * 3 };
}
const worldOpen = w => w <= 1 || save.free || wstat(w - 1).done / wstat(w - 1).total >= 0.6;
const stageOpen = (w, s) => s === 0 || save.free || !!save.done[sid(w, s - 1)] || !!save.done[sid(w, s)];
const totalStars = () => C.worlds.reduce((n, W, i) => n + wstat(i).stars, 0);

/* ---------- sonido ---------- */
const AU = window.LAudio, sfx = AU.sfx;
const MVOL = [0, 0.05, 0.09, 0.15, 0.24, 0.36], SVOL = [0, 0.3, 0.55, 0.8, 1, 1.25];
const applySound = () => AU.set({ sfx: save.sv > 0, music: save.mv > 0, mv: MVOL[save.mv], sv: SVOL[save.sv] });
applySound();
/* cada sección tiene su tema: portada, mapa, un tema por mundo (tranquilo en la teoría) y el de los jefes */
function songFor() {
  if (V.scr === 'title' || V.scr === 'map') return V.scr;
  const w = 'w' + C.worlds[V.w].k;
  if (V.scr === 'world' || ST.type === 'T') return w + 'c';
  return ST.stage.boss ? 'boss' : w;
}

/* ---------- navegación ---------- */
let V = { scr: 'title', w: 0, s: 0 };
let ST = null;      // estado de la etapa en curso
let FD = null;      // cuadro de fórmula abierto
let twTimer = null;
let lastTw = null;  // último texto que Minerva ya dijo letra a letra

function go(scr, w, s) {
  V = { scr, w: w == null ? V.w : w, s: s == null ? V.s : s };
  closeModal();
  lastTw = null;
  if (scr === 'stage') enterStage();
  render();
  app.scrollTop = 0;
}
function render() {
  clearInterval(twTimer);
  document.documentElement.style.setProperty('--wc', `var(--w${C.worlds[V.w].k})`);
  app.className = 'screen scr-' + V.scr + (V.scr === 'world' || V.scr === 'stage' ? ' w' + C.worlds[V.w].k : '');
  app.innerHTML = '<div class="fit">' + ({ title: scrTitle, map: scrMap, world: scrWorld, stage: scrStage })[V.scr]() + '</div>';
  AU.play(songFor());
  const sayEl = app.querySelector('.say[data-tw]');
  if (sayEl) {
    const key = sayEl.dataset.tw + '|' + sayEl.textContent;
    if (key !== lastTw) { lastTw = key; typewriter(sayEl); }
  }
  fit();
  if (V.scr === 'stage' && ST.type === 'P') {
    const sheet = app.querySelector('#sheet');
    if (sheet && (ST.flash != null || ST.playing)) sheet.scrollTop = sheet.scrollHeight;
  }
  padShow(); legend();
}
/* Ajusta la pantalla al alto de la consola para no tener que deslizar: primero limita la hoja de la
   prueba (que se desliza por dentro si es larga) y luego reduce todo en proporción, hasta un mínimo legible. */
const ZMIN = 0.62;
function fit() {
  const f = app.firstElementChild;
  if (!f || !f.classList.contains('fit')) return;
  const cs = getComputedStyle(app);
  const H = app.clientHeight - parseFloat(cs.paddingTop) - parseFloat(cs.paddingBottom);
  const W = app.clientWidth - parseFloat(cs.paddingLeft) - parseFloat(cs.paddingRight);
  if (H < 50 || W < 50) return;
  const sheet = f.querySelector('#sheet'), cols = f.querySelector('.proof .cols'), dlg = f.querySelector('.proof .main .dialog');
  const map = f.querySelector('.map'), opts = map && map.querySelector('.opts');
  let z = 1;
  const lay = () => {
    const w = W / z;
    f.style.width = w + 'px';
    f.style.minHeight = '0px';
    f.style.marginBottom = '0px';
    f.style.transform = z < 0.999 ? 'scale(' + z + ')' : '';
    f.classList.toggle('narrow', w < 800);
    f.classList.toggle('tiny', w < 600);
    if (opts) {   // las opciones ocupan el hueco que dejan las tarjetas en la última fila
      opts.style.gridColumn = '';
      const n = getComputedStyle(map).gridTemplateColumns.split(' ').filter(t => parseFloat(t) > 0).length || 1, r = (map.children.length - 1) % n;
      opts.style.gridColumn = 'span ' + (r ? n - r : n);
    }
    if (sheet) {
      sheet.style.maxHeight = '';
      const cap = f.classList.contains('narrow') ? Math.max(190, H / z * 0.42) : Math.max(190, H / z - cols.offsetTop - dlg.offsetHeight - 22);
      sheet.style.maxHeight = cap + 'px';
    }
    return f.scrollHeight;
  };
  let need = lay();
  if (map) {
    /* en el mapa el número de columnas cambia con el tamaño: se prueba de mayor a menor y gana el primero que cabe */
    for (z = 1; need * z > H + 1 && z > ZMIN; ) { z = Math.max(ZMIN, z - 0.02); need = lay(); }
  } else {
    for (let i = 0; i < 6 && need * z > H + 1 && z > ZMIN; i++) {
      z = Math.max(ZMIN, Math.min(z - 0.01, H / need));
      need = lay();
    }
  }
  /* una vez decidido el tamaño, la pantalla ocupa todo el alto y se descuenta el hueco que deja la reducción */
  f.style.minHeight = (H / z) + 'px';
  const full = Math.max(need, H / z);
  f.style.marginBottom = z < 0.999 ? (-full * (1 - z)) + 'px' : '0px';
}
let fitTimer = null;
window.addEventListener('resize', () => { clearTimeout(fitTimer); fitTimer = setTimeout(() => { fit(); padShow(); }, 80); });
if (document.fonts && document.fonts.ready) document.fonts.ready.then(() => fit());
const soundBtn = () => `<button class="btn sm snd${save.mv + save.sv === 0 ? ' off' : ''}" data-act="sound" aria-label="Volumen: música ${save.mv} de 5, efectos ${save.sv} de 5" title="Volumen">${ico('spk')}<i class="vb">${meter(save.mv)}</i></button>`;
function hud(title, back, sub) {
  return `<header class="hud">
    <button class="btn sm" data-act="${back}">${ico('back')}<span>Volver</span></button>
    <div class="hud-t"><h1>${title}</h1>${sub ? `<span class="hud-s">${sub}</span>` : ''}</div>
    <div class="hud-r"><span class="tot" title="Estrellas conseguidas">${ico('star')} ${totalStars()}</span>${soundBtn()}</div>
  </header>`;
}
const starsHTML = n => `<span class="stars" aria-label="${n} de 3 estrellas">${[1, 2, 3].map(i => `<i class="${i <= n ? 'on' : ''}">${ico('star')}</i>`).join('')}</span>`;

/* ---------- portada ---------- */
function scrTitle() {
  const any = Object.keys(save.done).length > 0;
  return `<section class="title">
    <div class="tsnd">${soundBtn()}</div>
    <div class="logo"><span class="l1">L<span class="acc">O</span>GICA</span><span class="l2">AXIOM<span class="acc">A</span>TICA</span></div>
    <p class="tag">Cálculo axiomático de Hilbert, de la lógica clásica a Gödel</p>
    <div class="hero">
      <div class="hero-owl">${owl(6, 'happy')}</div>
      <div class="hero-proof sheet static">
        ${staticRow([1, 0, 'P→Q', 'Premisa'])}${staticRow([2, 0, 'Q→R', 'Premisa', 'p'])}
        ${staticRow([3, 1, 'P', 'Supuesto', 'h'])}${staticRow([4, 1, 'Q', 'MP 1, 3'])}${staticRow([5, 1, 'R', 'MP 2, 4'])}
        ${staticRow([6, 0, 'P→R', 'TD 3–5'])}
      </div>
    </div>
    <button class="btn pri big" data-act="start"><span class="blink">${any ? 'CONTINUAR' : 'PULSA START'}</span></button>
    <div class="strip">${C.worlds.map((W, i) => `<span class="wbadge" style="--wc:var(--w${W.k})" title="${esc(W.logic)}">${raw(W.badge)}</span>`).join('')}</div>
  </section>`;
}

/* ---------- mapa ---------- */
function scrMap() {
  const themeName = { '': 'Auto', light: 'Día', dark: 'Noche' }[save.theme];
  return hud('MAPA DE MUNDOS', 'title') + `<div class="map">` + C.worlds.map((W, i) => {
    const s = wstat(i), open = worldOpen(i);
    return `<button class="wcard${open ? '' : ' locked'}" style="--wc:var(--w${W.k});--bgimg:var(--img-w${W.k})" data-act="world" data-w="${i}">
      <span class="wbadge">${raw(W.badge)}</span>
      <span class="winfo"><span class="wnum">MUNDO ${W.k}</span><b>${W.name}</b><span class="wlogic">${W.logic}</span></span>
      <span class="wprog">${open
        ? `<span class="pbar"><i style="width:${Math.round(100 * s.done / s.total)}%"></i></span><span class="cnt">${s.done}/${s.total} · ${ico('star')} ${s.stars}</span>`
        : `<span class="cnt lockmsg">${ico('lock')} Completa el 60 % del mundo anterior</span>`}</span>
    </button>`;
  }).join('') + `
  <div class="opts panel">
    <span class="mlabel">OPCIONES</span>
    <div class="optgrid">
    <button class="btn sm" data-act="free" aria-pressed="${save.free}">Modo libre: ${save.free ? 'sí' : 'no'}</button>
    <button class="btn sm" data-act="theme">Tema: ${themeName}</button>
    <button class="btn sm" data-act="wipe">Borrar progreso</button>
    </div>
    <span class="optnote">El modo libre abre todos los mundos y etapas.</span>
  </div></div>`;
}

/* ---------- mundo ---------- */
const TYPE = { T: ['book', 'Teoría'], P: ['⊢', 'Prueba'], M: ['⊨', 'Modelo'], Q: ['quiz', 'Preguntas'], TT: ['grid', 'Tabla'], GN: ['num', 'Codificación'], V: ['gear', 'Motor'] };
function scrWorld() {
  const W = C.worlds[V.w];
  return hud(W.name, 'map', W.logic) + `
  <div class="dialog small slim" data-act="twskip"><div class="who">${owl(2, 'neutral')}</div><div class="say" data-tw="W${V.w}">${tx(W.intro)}</div></div>
  <ol class="stages">` + W.stages.map((s, i) => {
    const d = save.done[sid(V.w, i)], open = stageOpen(V.w, i);
    const res = !open ? ico('lock') : isEx(s) ? starsHTML(d || 0) : d ? `<span class="done">${ico('check')}</span>` : '';
    return `<li><button class="srow t${s.t}${open ? '' : ' locked'}${d ? ' isdone' : ''}" data-act="stage" data-s="${i}">
      <span class="snum">${i + 1}</span>
      <span class="stype" title="${TYPE[s.t][1]}">${ico(TYPE[s.t][0])}</span>
      <span class="stitle">${esc(s.title)}${s.boss ? ' <em class="boss">JEFE</em>' : ''}${s.sys ? '<small>' + s.sys + '</small>' : ''}</span>
      <span class="sres">${res}</span></button></li>`;
  }).join('') + `</ol>`;
}

/* ---------- etapas ---------- */
function enterStage() {
  const s = C.worlds[V.w].stages[V.s];
  if (s.t === 'T') ST = { type: 'T', stage: s, page: 0 };
  if (s.t === 'Q') ST = { type: 'Q', stage: s, i: 0, wrong: 0, picked: -1, bad: [] };
  if (s.t === 'TT') {
    const cols = s.cols.map(L.parse), atoms = L.atomsOf(cols), rows = ttRows(atoms);
    ST = { type: 'TT', stage: s, cols, atoms, rows, cells: cols.map(() => rows.map(() => null)), mark: null, checks: 0, solved: false,
      msg: { k: 'info', h: tx(s.intro) } };
  }
  if (s.t === 'GN') {
    ST = { type: 'GN', stage: s, word: s.word, ans: s.word.map(() => null), cur: 0, mark: null, checks: 0, solved: false,
      msg: { k: 'info', h: tx(s.intro) } };
  }
  if (s.t === 'M') {
    const prem = s.prem.map(L.parse), goal = s.goal ? L.parse(s.goal) : null, val = {};
    const fs = goal ? [...prem, goal] : prem;
    const atoms = s.dom ? L.groundAtoms(fs, s.dom) : L.atomsOf(fs);   // con dominio: un valor por predicado e individuo
    atoms.forEach(a => { val[a] = 1; });
    ST = { type: 'M', stage: s, prem, goal, atoms, val, moves: 0, msg: { k: 'info', h: tx(s.intro) } };
  }
  if (s.t === 'V') {
    ST = { type: 'V', stage: s, prem: [], concl: null, sys: s.sys ? s.sys[0] : null, res: null, busy: false, got: {}, seen: {}, solved: false,
      msg: { k: 'info', h: tx(s.intro) } };
  }
  if (s.t === 'P') {
    const prem = s.prem.map(L.parse), goal = L.parse(s.goal);
    ST = { type: 'P', stage: s, goal, init: L.newProof(prem), st: L.newProof(prem), hist: [], sel: [], hints: 0,
      rules: L.ORDER.filter(r => C.RS[s.rules].includes(r)), flash: null, solved: false, usedSol: false, playing: false,
      msg: { k: 'info', h: tx(s.intro || 'Toca las líneas que quieres usar y pulsa una regla.') } };
  }
}
function scrStage() {
  const s = ST.stage, W = C.worlds[V.w];
  const head = hud(esc(s.title), 'toWorld', `Mundo ${W.k} · etapa ${V.s + 1} de ${W.stages.length}`);
  return head + ({ T: scrTheory, P: scrProof, M: scrModel, Q: scrQuiz, TT: scrTable, GN: scrGodel, V: scrLab })[ST.type]();
}
const KMOOD = { err: 'sad', hint: 'think', ok: 'happy' };
const sayBox = (m, small) => {
  const mood = KMOOD[m.k] || (ST.stage.boss ? 'brave' : 'neutral');
  return `<div class="dialog ${m.k}${small ? ' small' : ''}" data-act="twskip" aria-live="polite"><div class="who">${owl(3, mood)}</div><div class="say" data-tw="S${V.w}-${V.s}-${m.k}">${m.h}</div></div>`;
};

/* ----- teoría ----- */
function staticRow(r) {
  const flag = r[4] || '';
  const sub = flag === 'h' || flag === 's';
  return rowHTML({ n: r[0], depth: r[1], html: r[2] === '⋮' ? glyph('⋮') : fm(r[2]), just: raw(r[3]), top: sub, foot: sub || flag === 'p' });
}
function figHTML(f) {
  if (Array.isArray(f)) return `<div class="figrow">${f.map(figHTML).join('')}</div>`;
  if (f.k === 'fitch') return `<div class="sheet static">${f.rows.map(staticRow).join('')}</div>`;
  if (f.k === 'table') return `<div class="tw"><table class="tbl${f.tight ? ' tight' : ''}"><thead><tr>${f.head.map(h => `<th>${tx(h)}</th>`).join('')}</tr></thead><tbody>${f.rows.map(r => `<tr>${r.map(c => `<td>${tx(c)}</td>`).join('')}</tr>`).join('')}</tbody></table></div>`;
  if (f.k === 'kripke') {
    const BW = 104, BH = 46, pos = {};
    f.w.forEach(w => { pos[w.id] = w; });
    const arrows = f.e.map(([a, b]) => {
      const A = pos[a], B = pos[b];
      const x1 = A.x + BW + 6, y1 = A.y + BH / 2, x2 = B.x - 12, y2 = B.y + BH / 2;
      return `<line x1="${x1}" y1="${y1}" x2="${x2}" y2="${y2}"/><path d="M${x2 + 8} ${y2} l-10 -6 v12 z"/>`;
    }).join('');
    return `<div class="kr-wrap"><div class="kripke" style="height:${f.h}px"><svg viewBox="0 0 310 ${f.h}" width="310" height="${f.h}" aria-hidden="true">${arrows}</svg>${
      f.w.map(w => `<div class="world" style="left:${w.x}px;top:${w.y}px"><b>${w.id}</b><span>${tx('{' + (w.t || '–') + '}')}</span></div>`).join('')}</div>
      <p class="cap">${tx(f.cap)}</p></div>`;
  }
  return '';
}
function scrTheory() {
  const s = ST.stage, p = s.pages[ST.page], n = s.pages.length, last = ST.page === n - 1;
  const mood = p.mood || moodOf(p.say);
  return `<div class="theory">
    <div class="scene panel${p.fig ? '' : ' empty'}">${p.fig ? figHTML(p.fig) : `<div class="scene-owl">${owl(7, mood)}</div>`}</div>
    <div class="dialog big" data-act="twskip"><div class="who">${owl(4, mood)}<span>MINERVA</span></div><div class="say" data-tw="T${V.w}-${V.s}-${ST.page}">${tx(p.say)}</div></div>
    <div class="tnav">
      <button class="btn" data-act="tprev" ${ST.page ? '' : 'disabled'}>${ico('back')}<span>Atrás</span></button>
      <span class="pg">${s.pages.map((x, i) => `<i class="${i === ST.page ? 'on' : ''}"></i>`).join('')}</span>
      <button class="btn pri" data-act="tnext"><span>${last ? 'Terminar' : 'Siguiente'}</span>${ico('next')}</button>
    </div>
  </div>`;
}
/* Minerva escribe letra a letra, con su voz de pitidos, y mueve el pico mientras habla */
function typewriter(el) {
  const box = el.closest('.dialog');
  const bird = box && box.querySelector('.owl');
  if (bird) bird.classList.add('fresh');
  if (window.matchMedia('(prefers-reduced-motion: reduce)').matches) return;
  const units = [];
  const walk = node => {
    [...node.childNodes].forEach(ch => {
      if (ch.nodeType === 3) {
        const frag = document.createDocumentFragment();
        ch.textContent.split(/(\s+)/).forEach(tok => {
          if (!tok) return;
          if (/^\s+$/.test(tok)) { frag.appendChild(document.createTextNode(tok)); return; }
          const word = document.createElement('span');
          word.className = 'tww';
          for (const c of tok) { const sp = document.createElement('span'); sp.className = 'twh'; sp.textContent = c; word.appendChild(sp); units.push(sp); }
          frag.appendChild(word);
        });
        ch.replaceWith(frag);
      } else if (ch.nodeName.toLowerCase() === 'svg') { ch.classList.add('twh'); units.push(ch); }
      else walk(ch);
    });
  };
  walk(el);
  if (bird) bird.classList.add('talk');
  let i = 0, n = 0;
  twTimer = setInterval(() => {
    for (let k = 0; k < 2 && i < units.length; k++) units[i++].classList.remove('twh');
    if (n++ % 2 === 0) AU.blip();
    if (i >= units.length) { clearInterval(twTimer); if (bird) bird.classList.remove('talk'); }
  }, 30);
}
function twDone() {
  const hidden = app.querySelectorAll('.twh');
  if (!hidden.length) return true;
  clearInterval(twTimer);
  hidden.forEach(e => e.classList.remove('twh'));
  app.querySelectorAll('.owl.talk').forEach(o => o.classList.remove('talk'));
  return false;
}

/* ----- derivación de Hilbert ----- */
function rowHTML(o) {
  let bars = '';
  for (let d = 0; d <= o.depth; d++) {
    const last = d === o.depth;
    bars += `<i class="bar${last && o.top ? ' top' : ''}${last && o.foot ? ' foot' : ''}"></i>`;
  }
  return `<div class="row ${o.cls || ''}" ${o.attr || ''}><span class="ln">${o.n}</span><span class="bars">${bars}</span><span class="fml${o.foot ? ' foot' : ''}">${o.html}</span><span class="just">${o.just || ''}</span></div>`;
}
function sheetHTML() {
  const st = ST.st, S = st.open;
  const selL = new Set(ST.sel.filter(x => x > 0));
  const selS = ST.sel.filter(x => x < 0).map(x => L.subAt(st, -x));
  const nec = ST.rules.includes('Nec');
  let lastPrem = -1;
  st.lines.forEach((l, i) => { if (l.kind === 'prem') lastPrem = i; });
  let h = '';
  st.lines.forEach((ln, i) => {
    const k = L.lineK(st, i, S), cls = [];
    if (selL.has(i + 1) || selS.some(sp => i >= sp.start && i <= sp.end)) cls.push('sel');
    if (k < 0) cls.push(L.pickSub(st, i) ? 'insub' : 'dim');
    if (i === ST.flash) cls.push('new');
    if (nec && ln.kind === 'step' && !ln.deps.length) cls.push('thm');   // un teorema: no depende de premisas ni de supuestos
    const sub = ln.kind === 'hyp';
    h += rowHTML({
      n: i + 1, depth: ln.path.length, html: fh(ln.f),
      just: raw(ln.rule) + (ln.cites ? ' ' + ln.cites : ''), top: sub, foot: sub || i === lastPrem,
      cls: cls.join(' '), attr: `data-act="line" data-i="${i}" role="button" tabindex="0"`
    });
  });
  if (!ST.solved) h += rowHTML({ n: '', depth: S.length, html: '<span class="caret"></span>', cls: 'cursor' });
  return h;
}
function paletteHTML() {
  const st = ST.st, off = ST.solved || ST.playing ? 'disabled' : '';
  const lit = rid => { const r = L.apply(st, rid, ST.sel, {}, ST.goal); return !r.error && !r.need; };
  const hasHyp = ST.rules.some(r => ['TD', '¬I', '∨E', '∃E', '↔I'].includes(r));
  const btn = r => `<button class="rbtn${L.RULES[r].ax ? ' ax' : !off && lit(r) ? ' lit' : ''}" data-act="rule" data-r="${r}" title="${esc(L.RULES[r].name + ': ' + L.RULES[r].desc)}" ${off}>${raw(r)}</button>`;
  const axs = ST.rules.filter(r => L.RULES[r].ax), rls = ST.rules.filter(r => !L.RULES[r].ax);
  return `<div class="panel pal">
    ${axs.length ? `<div class="mlabel">AXIOMAS</div><div class="rules">${axs.map(btn).join('')}</div>` : ''}
    <div class="mlabel">REGLAS</div>
    <div class="rules">${rls.map(btn).join('')}</div>
    <div class="mlabel">SUBPRUEBAS</div>
    <div class="acts">
      ${hasHyp ? `<button class="btn sm" data-act="hyp" ${off}>Suponer</button>` : ''}
      <button class="btn sm" data-act="close" ${off || (st.open.length ? '' : 'disabled')}>Cerrar sub.</button>
    </div>
    <div class="acts tools">
      <button class="btn sm" data-act="undo" ${off || (ST.hist.length ? '' : 'disabled')}>${ico('undo')}<span>Deshacer</span></button>
      <button class="btn sm" data-act="reset" ${off || (ST.hist.length ? '' : 'disabled')}>Reiniciar</button>
      <button class="btn sm" data-act="hint" ${off}>Pista</button>
      <button class="btn sm" data-act="book">Reglas</button>
    </div>
    ${ST.rules.includes('Nec') ? '<p class="cap thmnote">Los números en verde marcan teoremas: líneas que no dependen de ninguna premisa ni supuesto. Solo a ellas se aplica ' + fm('Nec') + '.</p>' : ''}
  </div>`;
}
function goalHTML(tag, prem, goal, sym, sys) {
  return `<div class="goal panel"><span class="gtag">${tag}</span><span class="seq">${prem.map(fh).join('<span class="comma">,</span> ')} ${glyph(sym)} ${fh(goal)}</span>${sys ? `<span class="sys">${sys}</span>` : ''}</div>`;
}
const SYSNAME = { H: 'Hilbert a mano', K: 'Sistema K', T: 'Sistema T', S4: 'Sistema S4', S5: 'Sistema S5', K4: 'Sistema K4', LP: 'Lógica LP' };
function scrProof() {
  const s = ST.stage;
  return `<div class="proof">
    ${goalHTML('DEMUESTRA', ST.init.lines.map(l => l.f), ST.goal, '⊢', s.sys ? SYSNAME[s.sys] : '')}
    <div class="cols">
      <div class="main"><div class="sheet panel" id="sheet">${sheetHTML()}</div>${sayBox(ST.msg, true)}</div>
      <div class="side">${paletteHTML()}</div>
    </div>
  </div>`;
}
const IDLE = 'Toca las líneas que quieres usar y pulsa una regla.';
function say(k, h) { ST.msg = { k, h }; }
function commit(st) {
  ST.hist.push(ST.st);
  ST.st = st; ST.sel = []; ST.flash = st.lines.length - 1;
  if (ST.msg.k === 'err') say('info', IDLE);
  sfx.ok();
  checkWin();
  render();
}
function checkWin() {
  const last = ST.st.lines[ST.st.lines.length - 1];
  if (!last || last.kind !== 'step' || last.path.length || !L.eq(last.f, ST.goal)) return;
  ST.solved = true;
  const stars = ST.usedSol ? 1 : ST.hints ? 2 : 3;
  finish(stars);
  say('ok', '¡Demostrado! La conclusión está en la columna principal.');
  const mine = ST;
  setTimeout(() => { if (ST === mine && V.scr === 'stage') winModal(stars, `${ST.st.lines.length} líneas` + (ST.usedSol ? ' · con la solución' : ST.hints ? ` · ${ST.hints} ${ST.hints === 1 ? 'pista' : 'pistas'}` : ' · sin pistas')); }, 650);
}
function finish(stars) {
  const id = sid(V.w, V.s);
  save.done[id] = Math.max(save.done[id] || 0, stars);
  persist();
  sfx.win();
}
function doRule(rid, extra) {
  const r = L.apply(ST.st, rid, ST.sel, extra, ST.goal);
  if (r.error) { sfx.err(); say('err', raw(r.error)); closeModal(); render(); return; }
  if (r.need === 'schema') { openSchema(r, rid, extra); return; }
  if (r.need === 'formula') {
    openFormula(r.prompt, L.suggest(r.kind, ST.st, ST.goal, r.A), f => doRule(rid, Object.assign({}, extra, { f })));
    return;
  }
  if (r.need === 'choice') {
    openChoice(`${raw(rid)}: elige el resultado`, r.options, f => doRule(rid, Object.assign({}, extra, { out: L.str(f) })));
    return;
  }
  closeModal();
  commit(r.st);
}
function playSolution() {
  const mine = ST, sol = ST.stage.sol;
  ST.usedSol = true; ST.playing = true; ST.st = ST.init; ST.hist = []; ST.sel = []; ST.flash = null;
  say('hint', 'Mira cómo se construye, paso a paso.');
  render();
  let i = 0;
  const tick = () => {
    if (ST !== mine || V.scr !== 'stage') return;
    ST.st = L.step(ST.st, sol[i++], ST.goal);
    ST.flash = ST.st.lines.length - 1;
    sfx.sel();
    if (i >= sol.length) { ST.playing = false; checkWin(); render(); return; }
    render();
    setTimeout(tick, 800);
  };
  setTimeout(tick, 600);
}

/* ----- modelos ----- */
const VNAME = { 1: 'V', 0.5: 'A', 0: 'F' };
function scrModel() {
  const s = ST.stage, lp = s.logic === 'LP';
  const des = v => (lp ? v >= 0.5 : v === 1);
  const vals = lp ? [1, 0.5, 0] : [1, 0];
  const sat = s.mode === 'sat';   // consistencia: hay que hacerlas todas verdaderas
  const rowsF = sat ? ST.prem.map(f => ['Proposición', f, true]) : [...ST.prem.map(f => ['Premisa', f, true]), ['Conclusión', ST.goal, false]];
  let all = true;
  const rows = rowsF.map(([lab, f, want]) => {
    const v = L.evalF(f, ST.val, s.dom), good = des(v) === want;
    if (!good) all = false;
    return `<tr><td class="lab">${lab}</td><td>${fh(f)}</td><td><span class="vchip v${v * 2}">${VNAME[v]}</span></td>
      <td class="want ${good ? 'good' : 'no'}">${ico(good ? 'check' : 'cross')}<span>${want ? (lp ? 'debe ser V o A' : 'debe ser V') : (lp ? 'debe ser F' : 'debe ser F')}</span></td></tr>`;
  }).join('');
  ST.all = all;
  return `<div class="proof">
    ${sat ? `<div class="goal panel"><span class="gtag">CONSISTENCIA</span><span class="seq">${ST.prem.map(fh).join('<span class="comma">,</span> ')}</span><span class="sys">Lógica clásica</span></div>` : goalHTML('CONTRAEJEMPLO', ST.prem, ST.goal, '⊬', lp ? 'Lógica LP' : 'Lógica clásica')}
    <div class="cols">
      <div class="panel model">
        <div class="mlabel">VALORES</div>
        <div class="vals">${ST.atoms.map(a => `<div class="vrow"><span class="fm">${esc(a)}</span><span class="seg">${vals.map(v => `<button class="vbtn v${v * 2}${ST.val[a] === v ? ' on' : ''}" data-act="val" data-a="${a}" data-v="${v}" aria-pressed="${ST.val[a] === v}">${VNAME[v]}</button>`).join('')}</span></div>`).join('')}</div>
        ${s.dom ? `<p class="cap">Dominio: ${s.dom.join(', ')}</p>` : ''}
        <div class="mlabel">RESULTADO</div>
        <div class="tw"><table class="tbl vt"><tbody>${rows}</tbody></table></div>
        ${lp ? '<p class="cap">V: verdadera · A: ambas (verdadera y falsa) · F: falsa. Son designados V y A.</p>' : ''}
      </div>
      <div class="side">${sayBox(ST.msg, true)}</div>
    </div>
  </div>`;
}

/* ----- tablas de verdad ----- */
function ttRows(atoms) {
  const n = atoms.length, rows = [];
  for (let i = 0; i < (1 << n); i++) {
    const v = {};
    atoms.forEach((a, j) => { v[a] = (i >> (n - 1 - j)) & 1 ? 0 : 1; });
    rows.push(v);
  }
  return rows;
}
function scrTable() {
  const head = ST.atoms.map(a => `<th>${fm(a)}</th>`).join('') + ST.cols.map(f => `<th class="fc">${fh(f)}</th>`).join('');
  const body = ST.rows.map((v, r) => `<tr>${ST.atoms.map(a => `<td><span class="tv v${v[a] * 2}">${VNAME[v[a]]}</span></td>`).join('')}${ST.cols.map((f, c) => {
    const x = ST.cells[c][r], mk = ST.mark ? ST.mark[c][r] : '';
    return `<td class="fc"><button class="tcell${x == null ? ' empty' : ''}${mk ? ' ' + mk : ''}" data-act="tcell" data-c="${c}" data-r="${r}" aria-label="${esc(L.str(f))}, fila ${r + 1}: ${x == null ? 'vacía' : VNAME[x]}" ${ST.solved || mk === 'good' ? 'disabled' : ''}>${x == null ? '?' : VNAME[x]}</button></td>`;
  }).join('')}</tr>`).join('');
  const filled = ST.cells.every(col => col.every(x => x != null));
  return `<div class="proof">
    <div class="goal panel"><span class="gtag">TABLA DE VERDAD</span><span class="seq">${ST.cols.map(fh).join('<span class="comma">,</span> ')}</span><span class="sys">${ST.rows.length} filas</span></div>
    <div class="cols">
      <div class="panel model"><div class="tw"><table class="tbl tt"><thead><tr>${head}</tr></thead><tbody>${body}</tbody></table></div></div>
      <div class="side">${sayBox(ST.msg, true)}
        <div class="panel pal"><div class="acts">
          <button class="btn pri" data-act="tcheck" ${filled && !ST.solved ? '' : 'disabled'}>Comprobar</button>
          <button class="btn sm" data-act="tclear" ${ST.solved ? 'disabled' : ''}>Borrar todo</button></div>
          <p class="cap">Toca una casilla para poner V. Tócala otra vez para cambiarla a F.</p></div>
      </div>
    </div>
  </div>`;
}

/* ----- numeración de Gödel ----- */
const PRIMES = [2, 3, 5, 7, 11, 13];
const GCODE = new Map(C.GODEL);
const gnNumber = word => word.reduce((n, sym, i) => n * BigInt(PRIMES[i]) ** BigInt(GCODE.get(sym)), 1n);
const group = n => (String(n).length < 5 ? String(n) : String(n).replace(/\B(?=(\d{3})+(?!\d))/g, ' '));   // 2430, pero 20 212 500
function scrGodel() {
  const s = ST.stage, enc = s.mode === 'enc', n = group(gnNumber(ST.word));
  const slots = ST.word.map((sym, i) => {
    const a = ST.ans[i], mk = ST.mark ? ST.mark[i] : '';
    const body = enc
      ? `<span class="gtop">${fm(sym)}</span><span class="gpow">${PRIMES[i]}<sup>${a == null ? '?' : a}</sup></span>`
      : `<span class="gpow">${PRIMES[i]}<sup>${GCODE.get(sym)}</sup></span><span class="gbot">${a == null ? '?' : fm(a)}</span>`;
    return `<button class="gslot${i === ST.cur && !ST.solved ? ' cur' : ''}${mk ? ' ' + mk : ''}" data-act="gslot" data-i="${i}" ${ST.solved ? 'disabled' : ''}>${body}</button>`;
  }).join('');
  const pal = C.GODEL.map(([sym, code]) => `<button class="key" data-act="gpick" data-v="${enc ? code : esc(sym)}" ${ST.solved ? 'disabled' : ''}>${enc ? code : fm(sym)}</button>`).join('');
  const filled = ST.ans.every(x => x != null);
  return `<div class="proof">
    <div class="goal panel"><span class="gtag">${enc ? 'CODIFICA' : 'DECODIFICA'}</span><span class="seq">${enc ? fm(ST.word.join('')) + (ST.solved ? ' = ' + n : '') : n + (ST.solved ? ' = ' + fm(ST.word.join('')) : '')}</span></div>
    <div class="cols">
      <div class="panel model gn">
        <div class="mlabel">CLAVE</div>
        <div class="tw"><table class="tbl gtab"><tbody><tr>${C.GODEL.map(([sym]) => `<td>${fm(sym)}</td>`).join('')}</tr><tr>${C.GODEL.map(([sym, code]) => `<td>${code}</td>`).join('')}</tr></tbody></table></div>
        <div class="mlabel">TU RESPUESTA</div>
        <div class="gslots">${slots}</div>
        <div class="gpal">${pal}</div>
      </div>
      <div class="side">${sayBox(ST.msg, true)}
        <div class="panel pal"><div class="acts">
          <button class="btn pri" data-act="gcheck" ${filled && !ST.solved ? '' : 'disabled'}>Comprobar</button>
          <button class="btn sm" data-act="gclear" ${ST.solved ? 'disabled' : ''}>Borrar todo</button></div>
          <p class="cap">Toca una posición y luego elige su valor.</p></div>
      </div>
    </div>
  </div>`;
}

/* ----- motor de validez ----- */
const VAL = window.Validity;
const LOGICNAME = { cl: 'Lógica clásica', lp: 'Lógica LP', int: 'Lógica intuicionista' };
const GOALTXT = {
  valid: 'Analiza un argumento válido.',
  invalid: 'Encuentra un argumento no válido y mira su contraejemplo.',
  own: 'Escribe tú un argumento que no esté entre los ejemplos.',
  split: 'Haz que un mismo argumento sea válido en un sistema y no válido en otro.',
  gap: 'Encuentra un argumento válido en la lógica clásica que aquí no lo sea.'
};
const argKey = (prem, concl) => prem.map(L.str).sort().join(',') + '⊢' + L.str(concl);
function labEx(e) { return { prem: e[0].map(L.parse), concl: L.parse(e[1]), sys: e[3] }; }
function scrLab() {
  const s = ST.stage, off = ST.busy ? 'disabled' : '';
  const sysSel = s.sys
    ? `<span class="sysset">${s.sys.map(x => `<button class="btn sm${x === ST.sys ? ' on' : ''}" data-act="vsys" data-x="${x}" aria-pressed="${x === ST.sys}" ${off}>${x}</button>`).join('')}</span>`
    : `<span class="sys">${LOGICNAME[s.logic]}</span>`;
  const seq = `${ST.prem.map(fh).join('<span class="comma">,</span> ')} ${glyph('⊢')} ${ST.concl ? fh(ST.concl) : '<span class="qm">?</span>'}`;
  const prem = ST.prem.map((f, i) => `<button class="chip vc" data-act="vdel" data-i="${i}" title="Quitar" ${off}>${fh(f)}<i>${ico('cross')}</i></button>`).join('');
  const concl = ST.concl
    ? `<button class="chip vc" data-act="vdelc" title="Quitar" ${off}>${fh(ST.concl)}<i>${ico('cross')}</i></button>`
    : `<button class="chip add" data-act="vconc" ${off}>Escribir conclusión</button>`;
  const ex = s.ex.map((e, i) => { const x = labEx(e); return `<button class="chip ex" data-act="vex" data-i="${i}" ${off}>${x.prem.map(fh).join(', ')} ${glyph('⊢')} ${fh(x.concl)}${x.sys && s.sys ? `<small>${x.sys}</small>` : ''}</button>`; }).join('');
  const goals = s.goals.map(g => `<li class="${ST.got[g] ? 'on' : ''}">${ico(ST.got[g] ? 'check' : '□')}<span>${GOALTXT[g]}</span></li>`).join('');
  return `<div class="proof vlab">
    <div class="goal panel"><span class="gtag">MOTOR</span><span class="seq">${seq}</span>${sysSel}</div>
    <div class="cols">
      <div class="main">
        <div class="panel vbuild">
          <div class="mlabel">PREMISAS</div>
          <div class="chips">${prem}<button class="chip add" data-act="vadd" ${off}>+ Premisa</button></div>
          <div class="mlabel">CONCLUSIÓN</div>
          <div class="chips">${concl}</div>
          <div class="acts"><button class="btn pri" data-act="vrun" ${ST.concl && !ST.busy ? '' : 'disabled'}>Analizar</button>
            <button class="btn sm" data-act="vclear" ${off}>Vaciar</button></div>
        </div>
        ${labResult()}
        <div class="panel vexs"><div class="mlabel">EJEMPLOS</div><div class="chips">${ex}</div></div>
      </div>
      <div class="side">${sayBox(ST.msg, true)}
        <div class="panel mis"><div class="mlabel">MISIONES</div><ul>${goals}</ul></div>
      </div>
    </div>
  </div>`;
}
const vchip = v => `<span class="vchip v${v * 2}">${VNAME[v]}</span>`;
const bchip = b => `<span class="vchip v${b ? 2 : 0}">${VNAME[b ? 1 : 0]}</span>`;
function labResult() {
  const r = ST.res;
  if (!r) return '';
  const s = ST.stage;
  const [cls, icon, word] = r.v === 'valid' ? ['good', 'check', 'VÁLIDO'] : r.v === 'invalid' ? ['no', 'cross', 'NO VÁLIDO'] : ['unk', 'quiz', 'SIN DECIDIR'];
  const where = r.sys ? `<small>${r.sys}</small>` : '';
  const cmp = r.cmp ? `<p class="vcmp">En la lógica clásica: <b class="${r.cmp === 'valid' ? 'good' : 'no'}">${r.cmp === 'valid' ? 'válido' : r.cmp === 'invalid' ? 'no válido' : 'sin decidir'}</b></p>` : '';
  let body = '';
  if (s.table) body = truthTableHTML();
  else if (r.model) body = modelHTML(r.model);
  return `<div class="panel vres ${cls}"><div class="vverd">${ico(icon)}<span>${word}</span>${where}</div>${cmp}${body}</div>`;
}
/* Mundo 0: la tabla entera, con las filas de premisas verdaderas destacadas y los contraejemplos en rojo */
function truthTableHTML() {
  const fs = [...ST.prem, ST.concl], atoms = L.atomsOf(fs);
  if (atoms.length > 4) return ST.res.model ? modelHTML(ST.res.model) : '';
  const rows = ttRows(atoms);
  const head = atoms.map(a => `<th>${fm(a)}</th>`).join('') + ST.prem.map(f => `<th class="fc">${fh(f)}</th>`).join('') + `<th class="fc cc">${fh(ST.concl)}</th>`;
  const body = rows.map(v => {
    const pv = ST.prem.map(f => L.evalF(f, v)), cv = L.evalF(ST.concl, v), crit = pv.every(x => x === 1);
    return `<tr class="${crit ? (cv ? 'crit' : 'cex') : ''}">${atoms.map(a => `<td>${vchip(v[a])}</td>`).join('')}${pv.map(x => `<td class="fc">${vchip(x)}</td>`).join('')}<td class="fc cc">${vchip(cv)}</td></tr>`;
  }).join('');
  return `<div class="tw"><table class="tbl tt vtt"><thead><tr>${head}</tr></thead><tbody>${body}</tbody></table></div>
    <p class="cap">Con borde: filas con todas las premisas verdaderas. En rojo: además la conclusión es falsa.</p>`;
}
function evalRows(vals) {
  return `<div class="tw"><table class="tbl vt"><tbody>${ST.prem.map(f => `<tr><td class="lab">Premisa</td><td>${fh(f)}</td><td>${vals(f)}</td></tr>`).join('')}
    <tr><td class="lab">Conclusión</td><td>${fh(ST.concl)}</td><td>${vals(ST.concl)}</td></tr></tbody></table></div>`;
}
function modelHTML(M) {
  const lp = ST.stage.logic === 'lp';
  if (M.kind === 'val') {
    return `<div class="mlabel">CONTRAEJEMPLO</div><div class="gats">${M.atoms.map(a => `<span class="gat">${fm(a)} ${vchip(M.vals[a])}</span>`).join('')}</div>
      ${evalRows(f => vchip(L.evalF(f, M.vals)))}${lp ? '<p class="cap">V: verdadera · A: ambas · F: falsa. Son designados V y A.</p>' : ''}`;
  }
  if (M.kind === 'fo') {
    return `<div class="mlabel">CONTRAMODELO</div><p class="cap">Dominio: ${M.dom.join(', ')}</p>
      <div class="gats">${M.atoms.map(a => `<span class="gat">${fm(a)} ${vchip(M.vals[a])}</span>`).join('')}</div>
      ${evalRows(f => vchip(L.evalF(f, M.vals, M.dom)))}${lp ? '<p class="cap">V: verdadera · A: ambas · F: falsa. Son designados V y A.</p>' : ''}`;
  }
  const int = M.kind === 'int', g = f => (M.dom ? VAL.ground(f, M.dom) : f);
  const val = int ? f => bchip(VAL.iForce(g(f), 0, M)) : f => bchip(VAL.kEval(g(f), 0, M));
  const cap = int
    ? 'Cada flecha lleva a un estado que sabe más: lo establecido no se pierde. En w1 se establecen las premisas, pero no la conclusión.'
    : 'Las flechas son la accesibilidad. En w1 las premisas son verdaderas y la conclusión falsa.';
  return `<div class="mlabel">${int ? 'ESTADOS DE CONOCIMIENTO' : 'MODELO DE KRIPKE'}</div>${kripkeHTML(M, int)}
    <p class="cap">${cap}${M.dom ? ' Dominio: ' + M.dom.join(', ') + '.' : ''}${!int && M.R.some((r, i) => r.includes(i)) ? ' ' + ico('loop') + ' = el mundo se ve a sí mismo.' : ''}</p>
    ${evalRows(val)}`;
}
/* dibujo de un modelo: columnas por distancia a w1, flechas recortadas al borde de cada caja */
function kripkeHTML(M, int) {
  const n = M.W.length, E = [];
  if (int) M.edges.forEach(e => E.push(e));
  else M.R.forEach((r, i) => r.forEach(j => { if (j !== i) E.push([i, j]); }));
  const lev = new Array(n).fill(-1);
  lev[0] = 0;
  for (let q = [0]; q.length;) { const a = q.shift(); E.forEach(([x, y]) => { if (x === a && lev[y] < 0) { lev[y] = lev[a] + 1; q.push(y); } }); }
  lev.forEach((l, i) => { if (l < 0) lev[i] = 1; });
  const cols = [];
  lev.forEach((l, i) => { (cols[l] = cols[l] || []).push(i); });
  const BW = 112, BH = 52, GX = 64, GY = 16, rows = Math.max(...cols.map(c => c.length));
  const Wd = cols.length * (BW + GX) - GX, H = rows * (BH + GY) - GY, pos = [];
  cols.forEach((c, l) => c.forEach((i, k) => { pos[i] = { x: l * (BW + GX), y: (H - (c.length * (BH + GY) - GY)) / 2 + k * (BH + GY) }; }));
  const tip = (x, y, ux, uy) => `<path d="M${x} ${y} L${x - 11 * ux + 6 * uy} ${y - 11 * uy - 6 * ux} L${x - 11 * ux - 6 * uy} ${y - 11 * uy + 6 * ux} z"/>`;
  const seen = new Set();
  let svg = '';
  E.forEach(([a, b]) => {
    const k = Math.min(a, b) + '-' + Math.max(a, b);
    if (seen.has(k)) return;
    seen.add(k);
    const both = E.some(([x, y]) => x === b && y === a);
    const A = pos[a], B = pos[b], ax = A.x + BW / 2, ay = A.y + BH / 2, bx = B.x + BW / 2, by = B.y + BH / 2;
    const dx = bx - ax, dy = by - ay, d = Math.hypot(dx, dy) || 1, ux = dx / d, uy = dy / d;
    const t = Math.min((BW / 2 + 6) / (Math.abs(dx) || 1e-9), (BH / 2 + 6) / (Math.abs(dy) || 1e-9)) * d;
    const x1 = ax + ux * t, y1 = ay + uy * t, x2 = bx - ux * t, y2 = by - uy * t;
    svg += `<line x1="${x1}" y1="${y1}" x2="${x2}" y2="${y2}"/>` + tip(x2, y2, ux, uy) + (both ? tip(x1, y1, -ux, -uy) : '');
  });
  const boxes = M.W.map((w, i) => {
    const t = Object.keys(w).sort();
    const loop = !int && M.R[i].includes(i) ? `<em>${ico('loop')}</em>` : '';
    return `<div class="world${i === 0 ? ' root' : ''}" style="left:${pos[i].x}px;top:${pos[i].y}px;width:${BW}px;height:${BH}px"><b>w${i + 1}${loop}</b><span>${t.length ? fm(t.join(', ')) : '–'}</span></div>`;
  }).join('');
  return `<div class="kr-wrap"><div class="kmodel" style="width:${Wd}px;height:${H}px"><svg viewBox="0 0 ${Wd} ${H}" width="${Wd}" height="${H}" aria-hidden="true">${svg}</svg>${boxes}</div></div>`;
}
function labSay(r) {
  const s = ST.stage, lp = s.logic === 'lp', int = s.logic === 'int';
  if (r.v === 'valid') {
    if (r.how === 'table') return lp ? `¡Válido! Revisé las ${r.rows} valuaciones con V, A y F: en ninguna las premisas son designadas y la conclusión no.` : `¡Válido! Revisé las ${r.rows} valuaciones: en ninguna las premisas son verdaderas y la conclusión falsa.`;
    if (r.how === 'monadic') return '¡Válido! Con predicados de un solo lugar basta probar cada combinación de tipos de individuos, y ninguna es un contraejemplo.';
    if (r.how === 'kripke') return int ? '¡Válido! Ningún modelo de Kripke intuicionista lo refuta.' : `¡Válido en ${r.sys}! Ningún modelo de Kripke del sistema lo refuta.`;
    return '¡Válido! Supuse las premisas verdaderas y la conclusión falsa, y todas las ramas del árbol acabaron en contradicción.';
  }
  if (r.v === 'invalid') {
    if (r.model.kind === 'val') return lp ? 'No es válido. Con estos valores las premisas son designadas y la conclusión es falsa.' : 'No es válido. Con estos valores las premisas son verdaderas y la conclusión es falsa.';
    if (r.model.kind === 'fo') return lp ? 'No es válido. En este dominio las premisas son designadas y la conclusión es falsa.' : 'No es válido. En este dominio las premisas son verdaderas y la conclusión es falsa.';
    if (r.model.kind === 'int') return 'No es válido intuicionistamente. En el estado w1 están establecidas las premisas, pero no la conclusión.';
    return `No es válido en ${r.sys}. En el mundo w1 las premisas son verdaderas y la conclusión falsa.`;
  }
  if (r.how === 'big') return 'Es demasiado grande para mí. Prueba con menos letras o menos cajas.';
  return 'No he podido decidirlo. Con cuantificadores no hay un método que termine siempre (teorema de Church): no encontré un contramodelo pequeño ni cerré todas las ramas.';
}
function labGoals(r) {
  const s = ST.stage, got = ST.got, key = argKey(ST.prem, ST.concl);
  const isEx = s.ex.some(e => { const x = labEx(e); return argKey(x.prem, x.concl) === key; });
  if (r.v === 'valid') got.valid = 1;
  if (r.v === 'invalid') got.invalid = 1;
  if (!isEx && r.v !== 'unknown') got.own = 1;
  if (s.sys && r.v !== 'unknown') {
    const seen = ST.seen[key] = ST.seen[key] || {};
    seen[r.v] = 1;
    if (seen.valid && seen.invalid) got.split = 1;
  }
  if (r.v === 'invalid' && r.cmp === 'valid') got.gap = 1;
  if (!ST.solved && s.goals.every(g => got[g])) {
    ST.solved = true;
    finish(3);
    const mine = ST;
    setTimeout(() => { if (ST === mine && V.scr === 'stage') winModal(3, 'Misiones cumplidas'); }, 1400);
  }
}
function labRun() {
  if (!ST.concl || ST.busy) return;
  ST.busy = true; ST.res = null;
  say('hint', 'Analizando…');
  render();
  const mine = ST;
  setTimeout(() => {
    if (ST !== mine) return;
    const s = ST.stage;
    let r;
    try { r = VAL.check(s.logic, ST.sys, ST.prem, ST.concl); } catch (e) { r = { v: 'unknown', how: 'big' }; }
    r.sys = ST.sys;
    if (s.cmp) { try { r.cmp = VAL.check(s.cmp, null, ST.prem, ST.concl).v; } catch (e) { r.cmp = 'unknown'; } }
    ST.busy = false; ST.res = r;
    say(r.v === 'valid' ? 'ok' : 'hint', labSay(r));
    if (r.v === 'valid') sfx.ok(); else sfx.page();
    labGoals(r);
    render();
  }, 60);
}
function labSug() {
  const out = [], seen = new Set();
  ST.stage.ex.forEach(e => [...e[0], e[1]].forEach(x => { const f = L.parse(x), k = L.str(f); if (!seen.has(k)) { seen.add(k); out.push(f); } }));
  return out.slice(0, 10);
}
const labEdit = (title, put) => openFormula(title, labSug(), f => { closeModal(); put(f); ST.res = null; say('info', tx(ST.stage.intro)); sfx.ok(); render(); });

/* ----- preguntas ----- */
function scrQuiz() {
  const s = ST.stage, q = s.qs[ST.i], solved = ST.picked === q.ok;
  return `<div class="quiz">
    <div class="pg">${s.qs.map((x, i) => `<i class="${i === ST.i ? 'on' : i < ST.i ? 'past' : ''}"></i>`).join('')}</div>
    <div class="dialog big" data-act="twskip"><div class="who">${owl(4, solved ? 'happy' : ST.bad.length ? 'sad' : 'think')}<span>MINERVA</span></div><div class="say" data-tw="Q${V.w}-${V.s}-${ST.i}">${tx(q.q)}</div></div>
    <div class="qopts">${q.opts.map((o, i) => `<button class="btn qopt${solved && i === q.ok ? ' right' : ''}${ST.bad.includes(i) ? ' wrong' : ''}" data-act="qpick" data-i="${i}" ${solved || ST.bad.includes(i) ? 'disabled' : ''}>${tx(o)}</button>`).join('')}</div>
    ${solved ? `<div class="panel why"><b>${ico('check')} Correcto.</b> ${tx(q.why)}</div>
      <div class="tnav"><span></span><span></span><button class="btn pri" data-act="qnext"><span>${ST.i === s.qs.length - 1 ? 'Terminar' : 'Siguiente'}</span>${ico('next')}</button></div>`
      : ST.bad.length ? `<div class="panel why bad"><b>${ico('cross')} No es esa.</b> Piénsalo otra vez.</div>` : ''}
  </div>`;
}

/* ---------- ventanas ---------- */
function closeModal() {
  if (!modal.hidden) padKey = padKeyApp;
  modal.hidden = true; modal.innerHTML = ''; FD = null;
  padShow(); legend();
}
function showModal(html, cls) { modal.innerHTML = `<div class="mbox panel ${cls || ''}" role="dialog" aria-modal="true">${html}</div>`; if (modal.hidden) padKeyApp = padKey; modal.hidden = false; if (padOn) padSet(padDefault()); legend(); }

function alphabet() {
  if (ST.type === 'V') {   // motor: las letras de los ejemplos y de lo ya escrito, y los símbolos de la lógica del mundo
    const s = ST.stage, syms = [...s.syms], preds = new Set(), nm = new Set();
    let fo = syms.includes('∀');
    [...ST.prem, ...(ST.concl ? [ST.concl] : []), ...labSug()].forEach(f => L.subformulas(f).forEach(g => {
      if (g.t !== 'atom') return;
      preds.add(g.p);
      if (g.args.length) fo = true;
      g.args.forEach(a => { if (!L.VARS.includes(a)) nm.add(a); });
    }));
    (fo ? 'FG' : 'PQR').split('').forEach(c => preds.add(c));
    const terms = fo ? [...new Set([...nm, 'a', 'b'])].sort().concat(['x', 'y', 'z']) : [];
    return { preds: [...preds].sort(), terms, syms, fo };
  }
  const fs = [ST.goal, ...ST.st.lines.filter(l => l.f).map(l => l.f)];
  const preds = new Set(), sy = new Set();
  let fo = false;
  fs.forEach(f => L.subformulas(f).forEach(g => { if (g.t === 'atom') { preds.add(g.p); if (g.args.length) fo = true; } }));
  const txt = ST.rules.join('') + fs.map(L.str).join('');
  for (const c of '¬∧∨→↔⊥∀∃□◇') if (txt.includes(c)) sy.add(c);
  if (ST.rules.some(r => ['DN', 'DeM', 'LEM', 'QN'].includes(r))) ['¬', '∧', '∨'].forEach(c => sy.add(c));
  ST.rules.forEach(r => { for (const c of (L.RULES[r].syms || '')) sy.add(c); });
  if (ST.rules.some(r => ['T', '4', '5'].includes(r))) ['¬', '□', '◇'].forEach(c => sy.add(c));
  let terms = [];
  if (fo) {
    terms = L.namesInPlay(ST.st, ST.goal);
    const fr = L.freshName(ST.st, ST.goal);
    if (!terms.includes(fr)) terms.push(fr);
    if (sy.has('∀') || sy.has('∃')) terms.push('x', 'y');
  }
  if (!fo && FD && FD.slots) 'PQR'.split('').forEach(c => preds.add(c));
  return { preds: [...preds].sort(), terms, syms: [...'¬∧∨→↔⊥∀∃□◇'].filter(c => sy.has(c)), fo };
}
function openFormula(title, sug, onOK) {
  const al = alphabet();
  FD = { buf: '', onOK, sug, al };
  const key = (k, lab, cls) => `<button class="key ${cls || ''}" data-act="fkey" data-k="${esc(k)}">${lab || raw(k)}</button>`;
  showModal(`<h3>${tx(title)}</h3>
    ${sug.length ? `<div class="mlabel">SUGERENCIAS</div><div class="chips">${sug.map((f, i) => `<button class="chip" data-act="fsug" data-i="${i}">${fh(f)}</button>`).join('')}</div>` : ''}
    <div class="mlabel">O ESCRIBE OTRA</div>
    <div class="fdisp" id="fdisp"></div>
    <div class="fstat" id="fstat"></div>
    <div class="keys">
      <div class="krow">${al.preds.map(p => key(p)).join('')}${al.terms.map(t => key(t, null, 'term')).join('')}</div>
      <div class="krow">${al.syms.map(c => key(c)).join('')}${key('(')}${key(')')}${key('bs', ico('back') + ' Borrar', 'wide')}</div>
    </div>
    <div class="mrow"><button class="btn" data-act="mcancel">Cancelar</button><button class="btn pri" data-act="fok">Aceptar</button></div>
    <p class="cap kbd">Con teclado: ${al.syms.map(c => `<span><kbd>${esc(KEYOF[c])}</kbd>${glyph(c)}</span>`).join("")}<span><kbd>Intro</kbd>aceptar</span></p>`, 'fdlg');
  fdRefresh();
}
function fdParse(buf) {
  try {
    const f = L.parse(buf);
    if (!L.closed(f)) throw new L.LErr('Hay una variable suelta. Usa un nombre (a, b, c) o un cuantificador.');
    return { f };
  } catch (e) { if (e instanceof L.LErr) return { err: e.message }; throw e; }
}
const fdBuf = () => (FD.slots ? FD.slots[FD.cur].buf : FD.buf);
const fdCheck = () => fdParse(fdBuf());
function fdRefresh() {
  const d = document.getElementById('fdisp'), s = document.getElementById('fstat');
  if (FD && FD.slots) {
    const box = document.getElementById('fslots');
    if (!box) return;
    box.innerHTML = FD.slots.map((sl, i) => {
      const ok = sl.buf ? !!fdParse(sl.buf).f : null;
      return `<button class="slot${i === FD.cur ? ' cur' : ''}${ok === false ? ' bad' : ok ? ' good' : ''}" data-act="slotsel" data-i="${i}"><b>${esc(sl.label)}</b><span class="fm">${raw(sl.buf)}${i === FD.cur ? '<span class="caret"></span>' : ''}</span></button>`;
    }).join('');
  } else if (d) d.innerHTML = `<span class="fm">${raw(FD.buf)}</span><span class="caret"></span>`;
  if (!s) return;
  if (!fdBuf()) { s.className = 'fstat'; s.textContent = ''; return; }
  const r = fdCheck();
  s.className = 'fstat ' + (r.f ? 'good' : 'no');
  s.innerHTML = r.f ? ico('check') + ' Fórmula bien formada' : esc(r.err);
}
function fdKey(k) {
  const cur = FD.slots ? FD.slots[FD.cur] : FD;
  if (k === 'bs') cur.buf = [...cur.buf].slice(0, -1).join('');
  else if ([...cur.buf].length < 40) cur.buf += k;
  sfx.sel();
  fdRefresh();
}
function fdOK() {
  if (FD.slots) {
    const bad = FD.slots.findIndex(sl => !fdParse(sl.buf).f);
    if (bad >= 0) { sfx.err(); FD.cur = bad; fdRefresh(); return; }
    const args = {};
    FD.slots.forEach(sl => { args[sl.k] = fdParse(sl.buf).f; });
    const cb = FD.onSlots;
    cb(args);
    return;
  }
  const r = fdCheck();
  if (r.err) { sfx.err(); fdRefresh(); return; }
  const cb = FD.onOK;
  cb(r.f);
}
/* axiomas: se rellenan los huecos del esquema, cada uno con una fórmula */
function openSchema(r, rid, extra) {
  FD = { slots: r.slots.map(sl => ({ k: sl.k, label: sl.label, buf: '' })), cur: 0, sug: L.suggest('slot', ST.st, ST.goal), onSlots: args => doRule(rid, Object.assign({}, extra, { args })) };
  FD.al = alphabet();
  const al = FD.al;
  const key = (k, lab, cls) => `<button class="key ${cls || ''}" data-act="fkey" data-k="${esc(k)}">${lab || raw(k)}</button>`;
  showModal(`<h3>${raw(rid)}: <span class="fm">${raw(r.text)}</span></h3>
    <div class="mlabel">RELLENA LOS HUECOS</div>
    <div class="slots" id="fslots"></div>
    <div class="fstat" id="fstat"></div>
    ${FD.sug.length ? `<div class="mlabel">SUGERENCIAS PARA EL HUECO ACTIVO</div><div class="chips">${FD.sug.map((f, i) => `<button class="chip" data-act="fsug" data-i="${i}">${fh(f)}</button>`).join('')}</div>` : ''}
    <div class="keys">
      <div class="krow">${al.preds.map(p => key(p)).join('')}${al.terms.map(t => key(t, null, 'term')).join('')}</div>
      <div class="krow">${al.syms.map(c => key(c)).join('')}${key('(')}${key(')')}${key('bs', ico('back') + ' Borrar', 'wide')}</div>
    </div>
    <div class="mrow"><button class="btn" data-act="mcancel">Cancelar</button><button class="btn pri" data-act="fok">Aceptar</button></div>
    <p class="cap kbd">Con teclado: ${al.syms.map(c => `<span><kbd>${esc(KEYOF[c])}</kbd>${glyph(c)}</span>`).join("")}<span><kbd>Intro</kbd>aceptar</span></p>`, 'fdlg');
  fdRefresh();
}
function openChoice(title, opts, onPick) {
  FD = { opts, onPick, choice: true };
  showModal(`<h3>${title}</h3><div class="choices">${opts.map((f, i) => `<button class="btn chopt" data-act="cpick" data-i="${i}">${fh(f)}</button>`).join('')}</div>
    <div class="mrow"><button class="btn" data-act="mcancel">Cancelar</button></div>`);
}
const meter = v => [1, 2, 3, 4, 5].map(i => `<i class="${i <= v ? 'on' : ''}"></i>`).join('');
function openSound() {
  const row = (lab, k) => `<div class="vol"><b>${lab}</b>
    <button class="btn sm" data-act="vol" data-k="${k}" data-d="-1" aria-label="Bajar ${lab.toLowerCase()}" ${save[k] <= 0 ? 'disabled' : ''}>-</button>
    <span class="vmeter" role="img" aria-label="${lab}: ${save[k]} de 5">${meter(save[k])}</span>
    <button class="btn sm" data-act="vol" data-k="${k}" data-d="1" aria-label="Subir ${lab.toLowerCase()}" ${save[k] >= 5 ? 'disabled' : ''}>+</button></div>`;
  showModal(`<h3>Volumen</h3>${row('Música', 'mv')}${row('Efectos', 'sv')}
    <div class="mrow"><button class="btn pri" data-act="mcancel">Listo</button></div>`, 'snddlg');
}
function openBook() {
  showModal(`<h3>Libro de reglas</h3><div class="book">${ST.rules.map(r => { const R = L.RULES[r]; return `<div class="brow"><span class="rbtn static">${raw(r)}</span><div><b>${R.name}</b><p>${raw(R.desc)}</p><small>${R.use}</small></div></div>`; }).join('')}</div>
    <div class="mrow"><button class="btn pri" data-act="mcancel">Cerrar</button></div>`, 'bookdlg');
}
function winModal(stars, detail) {
  const W = C.worlds[V.w], last = V.s === W.stages.length - 1;
  const outro = ST.stage.outro ? `<p class="outro">${tx(ST.stage.outro)}</p>` : '';
  showModal(`<div class="winowl">${owl(4, 'happy')}</div><div class="qed">${ST.type === 'P' ? 'Q.E.D.' : '¡BIEN!'}</div>
    <div class="bigstars">${starsHTML(stars)}</div>
    <p class="detail">${detail}</p>${outro}
    <div class="mrow"><button class="btn" data-act="again">Repetir</button><button class="btn" data-act="toWorld">Etapas</button>
    <button class="btn pri" data-act="next"><span>${last ? 'Al mapa' : 'Siguiente'}</span>${ico('next')}</button></div>`, 'win');
}
function nextStage() {
  const W = C.worlds[V.w];
  if (V.s < W.stages.length - 1) go('stage', V.w, V.s + 1); else go('map');
}

/* ---------- acciones ---------- */
const ACT = {
  start() { sfx.ok(); go('map'); },
  title() { go('title'); },
  map() { go('map'); },
  toWorld() { go('world'); },
  sound() { openSound(); },
  vol(d) {
    save[d.k] = Math.max(0, Math.min(5, save[d.k] + (+d.d)));
    persist(); applySound(); sfx.sel();
    render(); openSound();
  },
  free() { save.free = !save.free; persist(); sfx.sel(); render(); },
  theme() { save.theme = { '': 'light', light: 'dark', dark: '' }[save.theme]; persist(); applyTheme(); sfx.sel(); render(); },
  wipe() {
    showModal(`<h3>¿Borrar todo el progreso?</h3><p>Se perderán las etapas completadas y las estrellas.</p>
      <div class="mrow"><button class="btn pri" data-act="mcancel">No, volver</button><button class="btn" data-act="wipeYes">Sí, borrar</button></div>`);
  },
  wipeYes() { save.done = {}; persist(); closeModal(); render(); },
  world(d) {
    if (!worldOpen(+d.w)) { sfx.err(); return; }
    sfx.sel(); go('world', +d.w);
  },
  stage(d) {
    if (!stageOpen(V.w, +d.s)) { sfx.err(); return; }
    sfx.sel(); go('stage', V.w, +d.s);
  },
  again() { go('stage'); },
  next() { nextStage(); },

  twskip() { twDone(); },
  tprev() { if (ST.page) { ST.page--; sfx.page(); render(); } },
  tnext() {
    if (!twDone()) return;
    if (ST.page < ST.stage.pages.length - 1) { ST.page++; sfx.page(); render(); return; }
    save.done[sid(V.w, V.s)] = 1; persist(); sfx.ok();
    nextStage();
  },

  line(d) {
    if (ST.type !== 'P' || ST.solved || ST.playing) return;
    const i = +d.i, st = ST.st, ln = st.lines[i], k = L.lineK(st, i, st.open);
    let ref = null;
    if (k >= 0) ref = i + 1;
    else { const sp = L.pickSub(st, i); if (sp) ref = -(sp.start + 1); }
    if (ref == null) {
      sfx.err(); say('err', 'Esa línea está dentro de una subprueba cerrada que ya no se puede citar desde aquí.'); render(); return;
    }
    const at = ST.sel.indexOf(ref);
    if (at >= 0) ST.sel.splice(at, 1); else ST.sel.push(ref);
    ST.flash = null;
    sfx.sel(); render();
  },
  rule(d) { ST.flash = null; doRule(d.r, {}); },
  hyp() { openFormula('¿Qué quieres suponer?', L.suggest('hyp', ST.st, ST.goal), f => { closeModal(); commit(L.addHyp(ST.st, f)); }); },
  close() { commit(L.closeSub(ST.st)); },
  undo() { if (!ST.hist.length) return; ST.st = ST.hist.pop(); ST.sel = []; ST.flash = null; say('info', IDLE); sfx.page(); render(); },
  reset() { ST.st = ST.init; ST.hist = []; ST.sel = []; ST.flash = null; say('info', tx(ST.stage.intro || IDLE)); sfx.page(); render(); },
  hint() {
    const hs = ST.stage.hints;
    if (ST.hints < hs.length) { ST.hints++; say('hint', `<b>Pista ${ST.hints} de ${hs.length}.</b> ` + tx(hs[ST.hints - 1])); }
    else say('hint', 'Ya te di todas las pistas. Si quieres, te enseño la prueba completa. <button class="btn sm" data-act="solve">Ver solución</button>');
    sfx.page(); render();
  },
  solve() { playSolution(); },
  book() { openBook(); },

  fkey(d) { fdKey(d.k); },
  fsug(d) {
    if (FD.slots) {
      FD.slots[FD.cur].buf = L.str(FD.sug[+d.i]);
      const next = FD.slots.findIndex((sl, i) => i > FD.cur && !sl.buf);
      if (next >= 0) FD.cur = next;
      sfx.sel(); fdRefresh(); return;
    }
    const cb = FD.onOK; cb(FD.sug[+d.i]);
  },
  slotsel(d) { FD.cur = +d.i; sfx.sel(); fdRefresh(); },
  fok() { fdOK(); },
  cpick(d) { const cb = FD.onPick; cb(FD.opts[+d.i]); },
  mcancel() { closeModal(); },

  tcell(d) {
    const c = +d.c, r = +d.r;
    ST.cells[c][r] = ST.cells[c][r] === 1 ? 0 : 1;
    if (ST.mark) ST.mark[c][r] = '';
    sfx.sel(); render();
  },
  tclear() { ST.cells = ST.cols.map(() => ST.rows.map(() => null)); ST.mark = null; say('info', tx(ST.stage.intro)); sfx.page(); render(); },
  tcheck() {
    ST.checks++;
    let bad = 0;
    ST.mark = ST.cols.map((f, c) => ST.rows.map((v, r) => { const ok = L.evalF(f, v) === ST.cells[c][r]; if (!ok) bad++; return ok ? 'good' : 'bad'; }));
    if (bad) {
      sfx.err();
      say('err', `Hay ${bad} ${bad === 1 ? 'casilla que no cuadra' : 'casillas que no cuadran'}, en rojo. Revisa el conector principal de esa columna.`);
      render(); return;
    }
    ST.solved = true;
    const stars = ST.checks === 1 ? 3 : ST.checks === 2 ? 2 : 1;
    finish(stars);
    say('ok', '¡Tabla correcta!');
    render();
    const mine = ST;
    setTimeout(() => { if (ST === mine && V.scr === 'stage') winModal(stars, mine.checks === 1 ? 'Correcta a la primera' : mine.checks + ' comprobaciones'); }, 600);
  },
  gslot(d) { ST.cur = +d.i; sfx.sel(); render(); },
  gpick(d) {
    ST.ans[ST.cur] = ST.stage.mode === 'enc' ? +d.v : d.v;
    if (ST.mark) ST.mark[ST.cur] = '';
    const next = ST.ans.findIndex((x, i) => x == null && i > ST.cur);
    ST.cur = next >= 0 ? next : (ST.ans.indexOf(null) >= 0 ? ST.ans.indexOf(null) : ST.cur);
    sfx.sel(); render();
  },
  gclear() { ST.ans = ST.word.map(() => null); ST.cur = 0; ST.mark = null; say('info', tx(ST.stage.intro)); sfx.page(); render(); },
  gcheck() {
    ST.checks++;
    const enc = ST.stage.mode === 'enc';
    let bad = 0;
    ST.mark = ST.word.map((sym, i) => { const ok = ST.ans[i] === (enc ? GCODE.get(sym) : sym); if (!ok) bad++; return ok ? 'good' : 'bad'; });
    if (bad) {
      ST.cur = ST.mark.indexOf('bad');
      sfx.err();
      say('err', `Hay ${bad} ${bad === 1 ? 'posición que no cuadra' : 'posiciones que no cuadran'}, en rojo. Mira otra vez la clave.`);
      render(); return;
    }
    ST.solved = true;
    const stars = ST.checks === 1 ? 3 : ST.checks === 2 ? 2 : 1;
    finish(stars);
    say('ok', '¡Codificación correcta!');
    render();
    const mine = ST;
    setTimeout(() => { if (ST === mine && V.scr === 'stage') winModal(stars, mine.checks === 1 ? 'Correcta a la primera' : mine.checks + ' comprobaciones'); }, 600);
  },
  val(d) {
    ST.val[d.a] = +d.v; ST.moves++;
    sfx.sel(); render();
    if (ST.all && !ST.solved) {
      ST.solved = true;
      const stars = ST.moves <= ST.atoms.length + 1 ? 3 : 2;
      finish(stars);
      const mine = ST;
      setTimeout(() => { if (ST === mine) winModal(stars, mine.stage.mode === 'sat' ? 'Todas verdaderas a la vez: el conjunto es consistente.' : 'Premisas designadas, conclusión no: el argumento no es válido.'); }, 500);
    }
  },
  qpick(d) {
    const q = ST.stage.qs[ST.i], i = +d.i;
    if (i === q.ok) { ST.picked = i; sfx.ok(); } else { ST.bad.push(i); ST.wrong++; sfx.err(); }
    render();
  },
  vadd() { labEdit('Escribe una premisa', f => { ST.prem.push(f); }); },
  vconc() { labEdit('Escribe la conclusión', f => { ST.concl = f; }); },
  vdel(d) { ST.prem.splice(+d.i, 1); ST.res = null; sfx.page(); render(); },
  vdelc() { ST.concl = null; ST.res = null; sfx.page(); render(); },
  vclear() { ST.prem = []; ST.concl = null; ST.res = null; say('info', tx(ST.stage.intro)); sfx.page(); render(); },
  vex(d) {
    const x = labEx(ST.stage.ex[+d.i]);
    ST.prem = x.prem; ST.concl = x.concl;
    if (x.sys && ST.stage.sys) ST.sys = x.sys;
    sfx.sel(); labRun();
  },
  vsys(d) { ST.sys = d.x; sfx.sel(); if (ST.concl) labRun(); else render(); },
  vrun() { labRun(); },
  qnext() {
    if (ST.i < ST.stage.qs.length - 1) { ST.i++; ST.picked = -1; ST.bad = []; sfx.page(); render(); return; }
    const stars = ST.wrong === 0 ? 3 : ST.wrong <= 2 ? 2 : 1;
    finish(stars);
    winModal(stars, ST.wrong ? `${ST.wrong} ${ST.wrong === 1 ? 'fallo' : 'fallos'}` : 'Sin fallos');
  }
};
/* ---------- mando: cruceta, A, B, L, R, START y SELECT ---------- */
let padOn = false;      // el cursor del mando solo se muestra cuando se está usando
let padKey = null, padKeyApp = null, padClick = false;
const keyOf = e => Object.keys(e.dataset).sort().map(k => k + '=' + e.dataset[k]).join('&');
function padCands() {
  const rootEl = modal.hidden ? app : modal;
  return [...rootEl.querySelectorAll('button:not(:disabled), .row[data-act]')].filter(e => e.offsetParent !== null && !e.classList.contains('locked') && !e.classList.contains('cursor'));
}
function padCur() { return padOn && padKey ? padCands().find(e => keyOf(e) === padKey) || null : null; }
function padShow() {
  document.querySelectorAll('.padf').forEach(e => e.classList.remove('padf'));
  const e = padCur();
  if (e) { e.classList.add('padf'); e.scrollIntoView({ block: 'nearest' }); }
  return e;
}
function padDefault() {
  const c = padCands();
  return c.find(e => e.classList.contains('pri')) || c.find(e => !e.closest('.hud') && !e.closest('.tsnd')) || c[0] || null;
}
function padSet(e) { padOn = true; padKey = e ? keyOf(e) : null; padShow(); }
function padMove(dir) {
  const cur = padCur();
  if (!cur) { padSet(padDefault()); return; }
  const r0 = cur.getBoundingClientRect(), x0 = r0.left + r0.width / 2, y0 = r0.top + r0.height / 2;
  let best = null, bs = Infinity;
  padCands().forEach(e => {
    if (e === cur) return;
    const r = e.getBoundingClientRect(), dx = r.left + r.width / 2 - x0, dy = r.top + r.height / 2 - y0;
    const horiz = dir === 'left' || dir === 'right';
    const along = dir === 'left' ? -dx : dir === 'right' ? dx : dir === 'up' ? -dy : dy;
    if (along < 6) return;
    /* si los dos elementos se solapan en el eje perpendicular, casi no se penaliza el desvío */
    const overlap = horiz ? Math.min(r0.bottom, r.bottom) - Math.max(r0.top, r.top) : Math.min(r0.right, r.right) - Math.max(r0.left, r.left);
    const across = Math.abs(horiz ? dy : dx);
    const score = along + across * (overlap > 4 ? 0.4 : 2.6);
    if (score < bs) { bs = score; best = e; }
  });
  if (best) { padSet(best); sfx.sel(); }
}
function padPress(k) {
  AU.unlock();
  const inModal = !modal.hidden, T = V.scr === 'stage' && ST ? ST.type : '';
  if (k === 'up' || k === 'down' || k === 'left' || k === 'right') {
    if (!inModal && T === 'T' && (k === 'left' || k === 'right')) { ACT[k === 'left' ? 'tprev' : 'tnext'](); return; }
    padMove(k); return;
  }
  if (k === 'A') {
    if (!inModal && app.querySelector('.twh')) { twDone(); return; }
    const cur = padCur();
    if (cur) { padClick = true; try { cur.click(); } finally { padClick = false; } return; }
    if (!inModal && V.scr === 'title') { ACT.start(); return; }
    if (!inModal && T === 'T') { ACT.tnext(); return; }
    padSet(padDefault()); return;
  }
  if (k === 'B') {
    if (inModal) { if (modal.querySelector('.win')) ACT.toWorld(); else closeModal(); sfx.page(); return; }
    const back = app.querySelector('.hud [data-act]');
    if (back) { sfx.page(); back.click(); }
    return;
  }
  if (k === 'start') {
    if (inModal) { if (modal.querySelector('.snddlg')) closeModal(); return; }
    if (V.scr === 'title') ACT.start(); else openSound();
    return;
  }
  if (inModal) return;
  if (V.scr === 'map' || V.scr === 'world') {
    if (k === 'L' || k === 'R') {
      const w = V.w + (k === 'L' ? -1 : 1);
      if (V.scr === 'world' && w >= 0 && w < C.worlds.length && worldOpen(w)) { sfx.sel(); go('world', w); }
    }
    return;
  }
  if (T === 'T') { if (k === 'L') ACT.tprev(); if (k === 'R') ACT.tnext(); return; }
  if (T === 'P' && !ST.solved && !ST.playing) {
    if (k === 'L') ACT.undo();
    if (k === 'R') ACT.hint();
    if (k === 'select') openBook();
    return;
  }
  if (T === 'TT' && !ST.solved) {
    if (k === 'R' && ST.cells.every(col => col.every(x => x != null))) ACT.tcheck();
    if (k === 'select') ACT.tclear();
    return;
  }
  if (T === 'GN' && !ST.solved) {
    if (k === 'R' && ST.ans.every(x => x != null)) ACT.gcheck();
    if (k === 'select') ACT.gclear();
    return;
  }
  if (T === 'V' && !ST.busy) {
    if (k === 'R') labRun();
    if (k === 'select') ACT.vclear();
    if (k === 'L' && ST.stage.sys) { const ss = ST.stage.sys; ACT.vsys({ x: ss[(ss.indexOf(ST.sys) + 1) % ss.length] }); }
    return;
  }
  if (T === 'Q' && k === 'R') { const n = app.querySelector('[data-act=qnext]'); if (n) n.click(); }
}
/* qué hace cada botón en la pantalla actual */
function legend() {
  const el = document.getElementById('legend');
  if (!el) return;
  const T = V.scr === 'stage' && ST ? ST.type : '';
  let items;
  if (!modal.hidden) items = [['A', 'elegir'], ['B', modal.querySelector('.win') ? 'etapas' : 'cerrar']];
  else if (V.scr === 'title') items = [['A', 'jugar'], ['START', 'jugar']];
  else if (V.scr === 'map') items = [['A', 'entrar'], ['B', 'portada'], ['START', 'volumen']];
  else if (V.scr === 'world') items = [['A', 'entrar'], ['B', 'mapa'], ['L R', 'otro mundo']];
  else if (T === 'T') items = [['A', 'seguir'], ['B', 'salir'], ['L R', 'página']];
  else if (T === 'P') items = [['A', 'elegir'], ['B', 'salir'], ['L', 'deshacer'], ['R', 'pista'], ['SELECT', 'reglas']];
  else if (T === 'TT') items = [['A', 'V / F'], ['B', 'salir'], ['R', 'comprobar'], ['SELECT', 'borrar']];
  else if (T === 'GN') items = [['A', 'elegir'], ['B', 'salir'], ['R', 'comprobar'], ['SELECT', 'borrar']];
  else if (T === 'V') items = [['A', 'elegir'], ['B', 'salir'], ['R', 'analizar'], ...(ST.stage.sys ? [['L', 'sistema']] : []), ['SELECT', 'vaciar']];
  else if (T === 'Q') items = [['A', 'elegir'], ['B', 'salir'], ['R', 'siguiente']];
  else items = [['A', 'elegir'], ['B', 'salir'], ['START', 'volumen']];
  el.innerHTML = items.map(([k, t]) => `<b>${k}</b> ${t}`).join(' · ');
}
document.querySelector('.pad').addEventListener('click', e => {
  const b = e.target.closest('[data-pad]');
  if (b) { padPress(b.dataset.pad); b.blur(); }
});

['pointerdown', 'pointerup', 'touchend', 'click', 'keydown'].forEach(ev => document.addEventListener(ev, () => AU.unlock(), true));
document.addEventListener('click', e => {
  if (e.target.closest('.pad')) return;
  if (!padClick && e.isTrusted && padOn) { padOn = false; padShow(); }
  const b = e.target.closest('[data-act]');
  if (!b || b.disabled) { if (e.target === modal && !modal.querySelector('.win')) closeModal(); return; }
  const fn = ACT[b.dataset.act];
  if (fn) fn(b.dataset, b);
});
const KEYOF = { '¬': '~', '∧': '&', '∨': '|', '→': '>', '↔': '=', '⊥': '#', '∀': '@', '∃': '?', '□': '[', '◇': '<' };
const KEYMAP = { '~': '¬', '!': '¬', '&': '∧', '^': '∧', '|': '∨', '>': '→', '=': '↔', '#': '⊥', '@': '∀', '?': '∃', '[': '□', '<': '◇', '(': '(', ')': ')' };
document.addEventListener('keydown', e => {
  if (e.ctrlKey && e.key.toLowerCase() === 'z' && V.scr === 'stage' && ST.type === 'P' && modal.hidden) { e.preventDefault(); ACT.undo(); return; }
  if (e.ctrlKey || e.metaKey || e.altKey) return;
  const DIR = { ArrowUp: 'up', ArrowDown: 'down', ArrowLeft: 'left', ArrowRight: 'right' }[e.key];
  if (DIR) { e.preventDefault(); padPress(DIR); return; }
  if (!modal.hidden && FD && !FD.choice) {   // se está escribiendo una fórmula: las letras van a la fórmula
    if (e.key === 'Escape') { closeModal(); return; }
    const al = FD.al;
    if (e.key === 'Enter') { e.preventDefault(); const cur = padCur(); if (cur) padPress('A'); else fdOK(); return; }
    if (e.key === 'Backspace') { e.preventDefault(); fdKey('bs'); return; }
    let k = KEYMAP[e.key];
    if (k && k !== '(' && k !== ')' && !al.syms.includes(k)) k = null;
    if (!k && /^[a-zA-Z]$/.test(e.key)) {
      if (al.preds.includes(e.key)) k = e.key;
      else if (al.terms.includes(e.key)) k = e.key;
      else if (al.preds.includes(e.key.toUpperCase()) && !al.fo) k = e.key.toUpperCase();
    }
    if (k) { e.preventDefault(); fdKey(k); }
    return;
  }
  /* un botón enfocado con el tabulador se activa de la forma habitual */
  const onCtl = e.target.matches && e.target.matches('button, .row[data-act]');
  if ((e.key === 'Enter' || e.key === ' ') && onCtl) {
    if (e.target.matches('.row[data-act]')) { e.preventDefault(); e.target.click(); }
    return;
  }
  const PADKEY = { z: 'A', x: 'B', a: 'L', s: 'R', enter: 'start', backspace: 'select', escape: 'B' }[e.key.toLowerCase()];
  if (PADKEY) { e.preventDefault(); padPress(PADKEY); }
});

/* icono de pestaña */
try {
  const link = document.createElement('link');
  link.rel = 'icon';
  link.href = 'data:image/svg+xml,' + encodeURIComponent(`<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" shape-rendering="crispEdges">${owlRects('neutral')}</svg>`);
  document.head.appendChild(link);
} catch (e) { /* sin icono */ }

/* textos fijos de la carcasa */
document.documentElement.lang = 'es';
document.title = 'Lógica Axiomática';
document.querySelector('.brand').innerHTML = 'L<span class="acc">O</span>GICA <b>AXIOM<span class="acc">A</span>TICA</b>';
document.querySelector('.pad').setAttribute('aria-label', 'Controles de la consola');
const PADTXT = { up: 'Arriba', down: 'Abajo', left: 'Izquierda', right: 'Derecha', L: 'L (tecla A)', R: 'R (tecla S)', A: 'A (tecla Z)', B: 'B (tecla X)', select: 'Select (Retroceso)', start: 'Start (Intro)' };
document.querySelectorAll('.pad [data-pad]').forEach(b => { b.title = PADTXT[b.dataset.pad]; b.setAttribute('aria-label', PADTXT[b.dataset.pad]); });

window.LogicaAxiomatica = { go, render, state: () => ST, owl };
render();
})();
