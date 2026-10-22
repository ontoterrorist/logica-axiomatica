/* Lógica Axiomática — Minerva, la lechuza (24×24) y sus expresiones */
(function (root) {
'use strict';

const BASE = [
  '........................',
  '.....CCCCCCCCCCCCCC.....',
  '....CCCCCCCCCCCCCCCC....',
  '..K....cccccccccc.T..K..',
  '.KBK...CCCCCCCCCC.T.KBK.',
  '.KBBKKKKKKKKKKKKKKTKBBK.',
  '.KBBBBBBBBBBBBBBBTTTBBK.',
  '.KBBBWWWWBBDDBBWWWWBBBK.',
  '.KBBWWWWWWBDDBWWWWWWBBK.',
  '.KBBWWHPWWBDDBWWHPWWBBK.',
  '.KBBWWPPWWBYYBWWPPWWBBK.',
  '.KBBWWWWWWBYYBWWWWWWBBK.',
  '.KBBBWWWWBBOOBBWWWWBBBK.',
  '.KBBBBBBBBBBBBBBBBBBBBK.',
  '..KBBBBBBBBBBBBBBBBBBK..',
  '..KDBBLLLLLLLLLLLLBBDK..',
  '.KDDBLLLMLLLLLLMLLLBDDK.',
  '.KDDBLLLLLLMMLLLLLLBDDK.',
  '.KDDBLLLMLLLLLLMLLLBDDK.',
  '.KDDBLLLLLLMMLLLLLLBDDK.',
  '..KDBBLLLLLLLLLLLLBBDK..',
  '...KKBBBBBBBBBBBBBBKK...',
  '....KYYYYK....KYYYYK....',
  '....KKKKKK....KKKKKK....'
];
const PAL = {
  K: '#2b2148', B: '#b0703f', D: '#844d2a', L: '#ffe2ac', M: '#e9bd7a', W: '#ffffff', P: '#1d1438', H: '#ffffff',
  Y: '#ffb52e', O: '#e8862a', C: '#4347a0', c: '#2f327a', T: '#ffcf2e', R: '#ff8fa0', S: '#7cc7ff'
};
/* ojos: 6×6 desde la fila 7; el izquierdo en la columna 4 y el derecho, reflejado, en la 14 */
const EYE = {
  blink: ['BBBBBB', 'BBBBBB', 'BBBBBB', 'KKKKKK', 'BBBBBB', 'BBBBBB'],
  happy: ['BBBBBB', 'BBKKBB', 'BKBBKB', 'KBBBBK', 'BBBBBB', 'BBBBBB'],
  sad: ['BBBBKK', 'BBKKWW', 'KKWWWW', 'WWHPWW', 'WWPPWW', 'BWWWWB'],
  think: ['BWWWWB', 'WWWHPW', 'WWWPPW', 'WWWWWW', 'WWWWWW', 'BWWWWB'],
  brave: ['BKKBBB', 'WWWKKB', 'WWWWWK', 'WWHPWW', 'WWPPWW', 'BWWWWB']
};
const SAME_SIDE = { think: true };
/* detalles fijos de cada expresión: [x, y, píxeles] */
const EXTRA = {
  happy: [[3, 11, 'RR'], [3, 12, 'RR'], [19, 11, 'RR'], [19, 12, 'RR'], [11, 11, 'PP']],
  sad: [[20, 7, 'S'], [20, 8, 'SS'], [20, 9, 'SS']],
  think: [[22, 0, 'T'], [21, 1, 'TTT'], [21, 2, 'TTT'], [22, 3, 'c']]
};
const SPARK = [[1, 0, 'T'], [0, 1, 'TTT'], [1, 2, 'T'], [22, 0, 'T'], [21, 1, 'TTT'], [22, 2, 'T']];
const BEAK_OPEN = [[11, 11, 'PP']];

const mirror = s => s.split('').reverse().join('').replace(/PH/g, 'HP');
function eyePatch(name) {
  const rows = EYE[name], out = [];
  rows.forEach((r, i) => {
    out.push([4, 7 + i, r]);
    out.push([14, 7 + i, SAME_SIDE[name] ? r : mirror(r)]);
  });
  return out;
}
/* parches que convierten la base en la expresión pedida */
function patches(mood) {
  let p = [];
  if (EYE[mood]) p = p.concat(eyePatch(mood));
  if (EXTRA[mood]) p = p.concat(EXTRA[mood]);
  return p;
}
function grid(mood) {
  const g = BASE.map(r => r.split(''));
  patches(mood).forEach(([x, y, s]) => { for (let i = 0; i < s.length; i++) g[y][x + i] = s[i]; });
  return g;
}

root.SPRITE = { N: 24, BASE, PAL, SPARK, BEAK_OPEN, patches, eyePatch, grid };
})(typeof window !== 'undefined' ? window : globalThis);
