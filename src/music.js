/* Lógica Axiomática — sonido: efectos, voz del texto y música por secciones (sintetizada, estilo GBA) */
(function (root) {
'use strict';

let ac = null, master = null, bus = null, sfxBus = null, noise = null, timer = null;
const waves = {};
const opt = { sfx: true, music: true, mv: 0.15, sv: 1 };   // mv y sv: ganancia de música y de efectos
let want = null;   // canción pedida
let cur = null;    // canción sonando

const SEMI = { C: 0, 'C#': 1, Db: 1, D: 2, 'D#': 3, Eb: 3, E: 4, F: 5, 'F#': 6, Gb: 6, G: 7, 'G#': 8, Ab: 8, A: 9, 'A#': 10, Bb: 10, B: 11 };
const QUAL = { '': [0, 4, 7], m: [0, 3, 7], 7: [0, 4, 7, 10], M7: [0, 4, 7, 11], m7: [0, 3, 7, 10], 6: [0, 4, 7, 9] };
const hzOf = (semi, oct) => 440 * Math.pow(2, (semi + (oct - 4) * 12 - 9) / 12);
function noteHz(n) { const m = /^([A-G][#b]?)(\d)$/.exec(n); return hzOf(SEMI[m[1]], +m[2]); }
function chord(sym) { const m = /^([A-G][#b]?)(.*)$/.exec(sym); return { root: SEMI[m[1]], iv: QUAL[m[2]] }; }

/* Cada compás: [acorde, melodía en ocho corcheas]. «-» silencio, «_» alarga la nota anterior.
   arp: índices de las notas del acorde · bass: r raíz, f quinta, o octava · drums: k bombo, s caja, h charles */
const SONGS = {
  title: { bpm: 132, lead: 'p25', arp: '0 2 1 2 0 2 1 2', bass: 'r - r - f - r r', drums: 'k h s h k k s h',
    bars: [['C', 'C5 - E5 G5 C6 _ _ G5'], ['G', 'B5 _ A5 G5 D5 _ G5 _'], ['Am', 'A4 - C5 E5 A5 _ G5 E5'], ['F', 'F5 _ A5 _ C6 _ A5 _'],
      ['Dm', 'D5 - F5 A5 D6 _ C6 A5'], ['G', 'B5 _ D6 _ G5 _ B5 _'], ['F', 'A5 G5 F5 E5 F5 _ A5 _'], ['G', 'G5 _ B5 _ D6 _ _ -']] },
  map: { bpm: 138, lead: 'square', arp: 'x 1 x 2 x 1 x 2', bass: 'r - f - r - f -', drums: 'k - h - s - h -',
    bars: [['G', 'D5 - G5 - B5 A5 G5 -'], ['C', 'E5 - G5 - C6 B5 G5 -'], ['G', 'D5 G5 B5 D6 B5 _ G5 -'], ['D', 'A5 _ F#5 _ D5 _ - -'],
      ['Em', 'E5 - G5 - B5 A5 G5 -'], ['C', 'E5 G5 C6 _ B5 _ A5 _'], ['D', 'F#5 _ A5 _ D6 _ C6 _'], ['G', 'B5 _ G5 _ G5 _ - -']] },
  w0: { bpm: 108, lead: 'p25', arp: '0 1 2 1 0 1 2 1', bass: 'r - - - f - - -', drums: 'k - h - s - h -',
    bars: [['C', 'E5 _ G5 _ C6 _ G5 _'], ['Am', 'A5 _ E5 _ C5 _ E5 _'], ['F', 'F5 _ A5 _ C6 _ A5 F5'], ['G', 'G5 _ B5 _ D6 _ B5 _'],
      ['C', 'E5 G5 C6 _ E6 _ D6 C6'], ['Em', 'B5 _ G5 _ E5 _ G5 B5'], ['F', 'A5 _ C6 _ A5 G5 F5 _'], ['G', 'G5 _ _ D5 G5 _ - -']] },
  w1: { bpm: 116, lead: 'p25', arp: '0 1 2 3 2 1 2 1', bass: 'r - - - f - - -', drums: 'k - h - - - h -',
    bars: [['F', 'A5 _ C6 _ A5 F5 G5 A5'], ['Bb', 'Bb5 _ D6 _ Bb5 _ F5 _'], ['C', 'G5 _ E5 G5 C6 _ Bb5 _'], ['F', 'A5 _ _ F5 C5 _ F5 _'],
      ['Dm', 'D5 F5 A5 _ D6 _ C6 A5'], ['Bb', 'Bb5 _ A5 G5 F5 _ D5 _'], ['C', 'E5 _ G5 _ C6 Bb5 G5 E5'], ['F', 'F5 _ _ _ - - C5 -']] },
  w2: { bpm: 104, lead: 'triangle', lv: 0.085, arp: '0 2 1 2 0 2 1 2', bass: 'r - - r - - f -', drums: 'k - h - - - h h',
    bars: [['Dm', 'D5 _ F5 _ A5 _ G5 F5'], ['C', 'E5 _ G5 _ C5 _ E5 _'], ['Bb', 'D5 _ F5 _ Bb5 _ A5 G5'], ['A', 'A5 _ _ E5 C#5 _ E5 _'],
      ['Dm', 'D5 F5 A5 D6 _ _ C6 A5'], ['Gm', 'Bb5 _ G5 _ D5 _ G5 Bb5'], ['A', 'A5 _ C#6 _ E6 _ C#6 A5'], ['Dm', 'D6 _ _ A5 F5 _ D5 _']] },
  w3: { bpm: 92, lead: 'sine', lv: 0.085, arp: '0 1 2 3 2 1 0 1', arpW: 'triangle', av: 0.04, bass: 'r - - - - - f -', drums: '- - - - h - - -', echo: 0.4,
    bars: [['FM7', 'A5 _ _ C6 E6 _ _ C6'], ['Em7', 'B5 _ _ G5 D6 _ B5 _'], ['Dm7', 'A5 _ F5 _ C6 _ A5 _'], ['CM7', 'G5 _ _ E5 B5 _ _ -'],
      ['FM7', 'A5 C6 E6 _ _ C6 A5 _'], ['G6', 'B5 _ D6 _ E6 _ D6 B5'], ['Am7', 'C6 _ _ A5 G5 _ E5 _'], ['G', 'D5 _ G5 _ B5 _ _ -']] },
  w4: { bpm: 100, lead: 'square', lv: 0.042, arp: 'x 0 x 2 x 1 x 2', bass: 'r - r - f - r -', drums: 'k - s - k s s -',
    bars: [['Am', 'A4 - A4 C5 E5 _ A5 _'], ['F', 'F5 _ A5 _ C6 _ A5 F5'], ['G', 'G5 _ B5 _ D6 _ B5 G5'], ['E', 'E5 _ G#5 _ B5 _ _ -'],
      ['Am', 'A5 - A5 C6 E6 _ D6 C6'], ['Dm', 'D6 _ A5 _ F5 _ D5 _'], ['E', 'E5 G#5 B5 _ E6 _ D6 B5'], ['Am', 'A5 _ _ E5 A4 _ - -']] },
  w5: { bpm: 132, lead: 'p12', lv: 0.055, arp: 'x 0 x 1 x 2 x 1', bass: 'r - f - r - f -', drums: 'k h s h k h s s',
    bars: [['C', 'E5 - G5 - E5 - C5 -'], ['Am', 'E5 - A5 - E5 - C5 -'], ['F', 'F5 - A5 - C6 - A5 -'], ['G', 'B5 A5 G5 F#5 G5 - D5 -'],
      ['C', 'E5 G5 C6 - G5 - E5 -'], ['E', 'E5 G#5 B5 - G#5 - E5 -'], ['F', 'A5 - C6 - F6 - C6 A5'], ['G', 'G5 - B5 - D6 D6 - -']] },
  w6: { bpm: 84, lead: 'triangle', lv: 0.09, arp: '0 - - 2 - - 1 -', arpW: 'p12', bass: 'r - - - - - - r', drums: 'k - - - - - h -', echo: 0.45,
    bars: [['Em', 'E5 _ _ _ G5 _ B5 _'], ['F', 'A5 _ _ F5 _ _ C5 _'], ['Em', 'B4 _ E5 _ G5 _ _ F#5'], ['Dm', 'F5 _ _ D5 A4 _ _ -'],
      ['Em', 'E5 _ G5 _ B5 _ E6 _'], ['C', 'E6 _ C6 _ G5 _ E5 _'], ['Am', 'A5 _ _ E5 C5 _ A4 _'], ['B', 'B4 _ D#5 _ F#5 _ _ -']] },
  w7: { bpm: 108, lead: 'p25', arp: '0 1 2 1 0 1 2 1', bass: 'r - - - f - - -', drums: 'k - h - - h h -',
    bars: [['G', 'B5 _ D6 _ G5 _ B5 _'], ['Em', 'G5 _ B5 _ E5 _ G5 _'], ['C', 'E5 _ G5 _ C6 _ B5 A5'], ['D', 'A5 _ F#5 _ D5 _ A5 _'],
      ['G', 'B5 D6 G6 _ D6 _ B5 _'], ['Bm', 'F#5 _ B5 _ D6 _ B5 _'], ['C', 'E6 _ D6 C6 G5 _ E5 _'], ['D', 'F#5 _ A5 _ D6 _ _ -']] },
  w8: { bpm: 80, lead: 'triangle', lv: 0.09, arp: '0 - 2 - 1 - 2 -', arpW: 'p12', bass: 'r - - - - - r -', drums: 'k - - - - - h -', echo: 0.45,
    bars: [['Cm', 'C5 _ _ Eb5 G5 _ _ Eb5'], ['Ab', 'Ab5 _ _ Eb5 C5 _ Eb5 _'], ['Fm', 'F5 _ Ab5 _ C6 _ Ab5 _'], ['G', 'G5 _ _ B4 D5 _ G5 _'],
      ['Cm', 'C6 _ G5 _ Eb5 _ C5 _'], ['Eb', 'Eb5 _ G5 _ Bb5 _ G5 _'], ['Ab', 'Ab5 _ C6 _ Eb6 _ C6 _'], ['G', 'D6 _ B5 _ G5 _ _ -']] },
  w9: { bpm: 96, lead: 'p25', arp: '0 1 2 3 2 1 2 1', bass: 'r - - r - - f -', drums: 'k - h - s - h h', echo: 0.3,
    bars: [['Dm', 'D5 _ A5 _ F5 _ D6 _'], ['Bb', 'D6 _ Bb5 _ F5 _ Bb5 _'], ['F', 'C6 _ A5 _ F5 _ A5 _'], ['C', 'G5 _ E5 _ C5 _ E5 G5'],
      ['Dm', 'A5 _ D6 _ F6 _ E6 D6'], ['Gm', 'D6 _ Bb5 _ G5 _ Bb5 _'], ['A', 'C#6 _ A5 _ E5 _ A5 C#6'], ['Dm', 'D6 _ _ _ A5 _ D5 -']] },
  boss: { bpm: 152, lead: 'p25', arp: '0 2 1 2 0 2 1 2', bass: 'r r o r r r o r', drums: 'k h s h k k s h',
    bars: [['Am', 'A5 A5 - A5 C6 - A5 -'], ['Am', 'E6 - D6 C6 A5 - G5 -'], ['F', 'F5 F5 - F5 A5 - C6 -'], ['G', 'D6 - B5 G5 B5 - D6 -'],
      ['Am', 'A5 A5 - A5 C6 - E6 -'], ['Am', 'E6 D6 C6 B5 A5 - E5 -'], ['F', 'F5 A5 C6 F6 _ - C6 -'], ['E', 'E6 _ B5 _ G#5 _ B5 -']] }
};
/* versión tranquila de cada mundo, para la teoría y la lista de etapas */
for (let i = 0; i <= 9; i++) {
  const s = SONGS['w' + i];
  SONGS['w' + i + 'c'] = Object.assign({}, s, { bpm: Math.round(s.bpm * 0.82), lead: 'triangle', lv: 0.085, arpW: 'sine', av: 0.035, bass: 'r - - - f - - -', drums: null, echo: 0.38 });
}
Object.keys(SONGS).forEach(id => {
  const s = SONGS[id], steps = [];
  s.bars.forEach(([ch, mel]) => { const c = chord(ch); mel.split(' ').forEach((tok, i) => steps.push({ c, tok, i })); });
  const lead = [];
  for (let i = 0; i < steps.length; i++) {
    const tk = steps[i].tok;
    if (tk === '-' || tk === '_') continue;
    let len = 1;
    while (i + len < steps.length && steps[i + len].tok === '_') len++;
    lead[i] = { f: noteHz(tk), len };
  }
  s.c = { steps, lead, arp: s.arp.split(' '), bass: s.bass.split(' '), drums: s.drums ? s.drums.split(' ') : null };
});

function pulse(duty) {
  const n = 32, re = new Float32Array(n), im = new Float32Array(n);
  for (let k = 1; k < n; k++) re[k] = 2 / (k * Math.PI) * Math.sin(k * Math.PI * duty);
  return ac.createPeriodicWave(re, im);
}
function ctx() {
  if (ac) return ac;
  if (root.LA_NO_AUDIO) return null;   // capturas de video: sin audio en vivo
  const AC = window.AudioContext || window.webkitAudioContext;
  if (!AC) return null;
  ac = new AC();
  const comp = ac.createDynamicsCompressor();
  master = ac.createGain(); master.gain.value = 0.9;
  master.connect(comp); comp.connect(ac.destination);
  bus = ac.createGain(); bus.gain.value = opt.mv; bus.connect(master);
  sfxBus = ac.createGain(); sfxBus.gain.value = opt.sv; sfxBus.connect(master);
  waves.p25 = pulse(0.25); waves.p12 = pulse(0.125);
  const len = ac.sampleRate, buf = ac.createBuffer(1, len, len), d = buf.getChannelData(0);
  for (let i = 0; i < len; i++) d[i] = Math.random() * 2 - 1;
  noise = buf;
  timer = setInterval(tick, 40);
  return ac;
}
function voice(wave, f, t, dur, vol, dest, pluck) {
  const o = ac.createOscillator(), g = ac.createGain();
  if (waves[wave]) o.setPeriodicWave(waves[wave]); else o.type = wave;
  o.frequency.value = f;
  g.gain.setValueAtTime(0.0001, t);
  g.gain.linearRampToValueAtTime(vol, t + 0.006);
  if (pluck) g.gain.exponentialRampToValueAtTime(vol * 0.12, t + dur);
  else g.gain.setValueAtTime(vol, Math.max(t + 0.006, t + dur - 0.035));
  g.gain.linearRampToValueAtTime(0.0001, t + dur + 0.004);
  o.connect(g); g.connect(dest);
  o.start(t); o.stop(t + dur + 0.03);
}
function drum(kind, t, dest) {
  const g = ac.createGain();
  g.connect(dest);
  if (kind === 'k') {
    const o = ac.createOscillator();
    o.type = 'sine';
    o.frequency.setValueAtTime(150, t);
    o.frequency.exponentialRampToValueAtTime(46, t + 0.11);
    g.gain.setValueAtTime(0.2, t);
    g.gain.exponentialRampToValueAtTime(0.0001, t + 0.14);
    o.connect(g); o.start(t); o.stop(t + 0.16);
    return;
  }
  const src = ac.createBufferSource(), f = ac.createBiquadFilter(), hat = kind === 'h', dur = hat ? 0.04 : 0.13;
  src.buffer = noise;
  f.type = 'highpass'; f.frequency.value = hat ? 7000 : 1600;
  g.gain.setValueAtTime(hat ? 0.03 : 0.07, t);
  g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
  src.connect(f); f.connect(g);
  src.start(t, Math.random() * 0.5); src.stop(t + dur + 0.02);
}
function schedStep(m, i, t) {
  const s = m.song, c = s.c, st = c.steps[i], d = m.stepDur, bi = st.i;
  const le = c.lead[i];
  if (le) voice(s.lead, le.f, t, le.len * d * 0.94, s.lv || 0.048, m.g);
  const a = c.arp[bi];
  if (a !== 'x' && a !== '-') {
    const iv = st.c.iv, k = +a;
    const semi = k < iv.length ? iv[k] : iv[k - iv.length] + 12;
    voice(s.arpW || 'p12', hzOf(st.c.root + semi, st.c.root >= 7 ? 3 : 4), t, d * 0.85, s.av || 0.024, m.g, true);
  }
  const b = c.bass[bi];
  if (b !== '-') voice('triangle', hzOf(st.c.root + (b === 'f' ? 7 : b === 'o' ? 12 : 0), st.c.root >= 7 ? 2 : 3), t, d * 0.9, 0.11, m.g);
  if (c.drums && c.drums[bi] !== '-') drum(c.drums[bi], t, m.g);
}
function tick() {
  if (!cur || ac.state !== 'running') return;
  const now = ac.currentTime;
  if (cur.next < now - 0.05) cur.next = now + 0.05;
  while (cur.next < now + 0.16) {
    schedStep(cur, cur.step, cur.next);
    cur.next += cur.stepDur;
    cur.step = (cur.step + 1) % cur.song.c.steps.length;
  }
}
function stopSong() {
  if (!cur) return;
  const m = cur, now = ac.currentTime;
  cur = null;
  m.g.gain.cancelScheduledValues(now);
  m.g.gain.setTargetAtTime(0, now, 0.12);
  setTimeout(() => { try { m.g.disconnect(); m.wet.disconnect(); } catch (e) { /* ya desconectado */ } }, 1500);
}
function startSong(id) {
  const song = SONGS[id], now = ac.currentTime, stepDur = 30 / song.bpm;
  const g = ac.createGain(), delay = ac.createDelay(1), fb = ac.createGain(), wet = ac.createGain();
  g.gain.setValueAtTime(0, now);
  g.gain.linearRampToValueAtTime(1, now + 0.5);
  delay.delayTime.value = stepDur * 1.5;
  fb.gain.value = 0.3; wet.gain.value = song.echo || 0.2;
  g.connect(bus); g.connect(delay); delay.connect(fb); fb.connect(delay); delay.connect(wet); wet.connect(bus);
  cur = { id, song, g, wet, stepDur, step: 0, next: now + 0.12 };
}
function sync() {
  if (!ac) return;
  const id = opt.music ? want : null;
  if (cur && cur.id === id) return;
  stopSong();
  if (id && SONGS[id]) startSong(id);
}
function sfxTone(freq, dur, when, type, vol) {
  if (!opt.sfx || !ctx()) return;
  voice(type || 'square', freq, ac.currentTime + (when || 0), dur, vol || 0.05, sfxBus, true);
}
function duck(sec) {
  if (!ac) return;
  const now = ac.currentTime;
  bus.gain.cancelScheduledValues(now);
  bus.gain.setTargetAtTime(opt.mv * 0.25, now, 0.04);
  bus.gain.setTargetAtTime(opt.mv, now + sec, 0.25);
}
const VOICE = [659.3, 740, 784, 880, 987.8];
const api = {
  /* primer gesto del jugador: el navegador solo deja sonar a partir de aquí */
  unlock() { try { if (ctx() && ac.state === 'suspended') ac.resume(); sync(); } catch (e) { /* sin audio */ } },
  set(o) {
    Object.assign(opt, o);
    try {
      if (ac) {
        const now = ac.currentTime;
        bus.gain.cancelScheduledValues(now);
        bus.gain.setTargetAtTime(opt.mv, now, 0.05);
        sfxBus.gain.setTargetAtTime(opt.sv, now, 0.05);
      }
      sync();
    } catch (e) { /* sin audio */ }
  },
  info() { return { state: ac ? ac.state : 'sin iniciar', song: cur ? cur.id : null, step: cur ? cur.step : null, want }; },
  play(id) { want = id; try { sync(); } catch (e) { /* sin audio */ } },
  /* voz de Minerva: un pitido por cada pocas letras, como los cuadros de diálogo de GBA */
  blip() { try { sfxTone(VOICE[Math.floor(Math.random() * VOICE.length)], 0.045, 0, 'p25', 0.032); } catch (e) { /* sin audio */ } },
  sfx: {
    sel: () => sfxTone(880, 0.06),
    page: () => sfxTone(620, 0.05),
    ok: () => { sfxTone(660, 0.08); sfxTone(990, 0.12, 0.07); },
    err: () => { sfxTone(196, 0.14, 0, 'sawtooth', 0.06); sfxTone(147, 0.2, 0.1, 'sawtooth', 0.06); },
    win: () => { duck(1.3); [523, 659, 784, 1047, 784, 1047, 1319].forEach((f, i) => sfxTone(f, i === 6 ? 0.5 : 0.16, i * 0.11, 'p25', 0.07)); }
  }
};
Object.keys(api.sfx).forEach(k => { const f = api.sfx[k]; api.sfx[k] = () => { try { f(); } catch (e) { /* sin audio */ } }; });
if (typeof document !== 'undefined') {
  document.addEventListener('visibilitychange', () => {
    if (!ac) return;
    if (document.hidden) ac.suspend(); else if (opt.music || opt.sfx) ac.resume();
  });
}
root.LAudio = api;
root.LAudioSongs = SONGS;
})(typeof window !== 'undefined' ? window : globalThis);
