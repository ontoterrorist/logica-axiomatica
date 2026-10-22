# Lógica Axiomática

Juego de estilo Game Boy Advance para aprender lógica formal con el **cálculo axiomático de Hilbert**. Es la hermana de Lógica Advance: los mismos diez mundos y la misma guía, Minerva la lechuza, pero en vez de deducción natural estilo Fitch las pruebas son derivaciones de Hilbert: axiomas, modus ponens y pocas reglas más. Solo en español.

**Jugar:** https://ontoterrorist.github.io/logica-axiomatica/

| Mundo | Lógica | Cálculo |
|---|---|---|
| 0 · Campamento Base | proposiciones, tablas de verdad, consistencia y validez | semántica |
| 1 · Pradera Proposicional | proposicional clásica | A1–A14 y MP |
| 2 · Bosque de los Cuantificadores | primer orden | Q1–Q4 y generalización |
| 3 · Archipiélago de los Mundos | modal K, T, S4 y S5 | axiomas K, T, 4 y 5 y necesitación |
| 4 · Ciudadela De Re | modal de primer orden (dominio constante) | axioma de Barcan |
| 5 · Taller del Constructor | intuicionista | A10 se cambia por A10i |
| 6 · Caverna de las Contradicciones | LP, la lógica paraconsistente | tercero excluido y reglas, sin modus ponens |
| 7 · Jardín de los Testigos | intuicionista de primer orden | |
| 8 · Abismo de las Paradojas | LP de primer orden | |
| 9 · Torre de Gödel | numeración de Gödel, incompletud, K4 y GL | K, 4 y necesitación |

## Cómo se juega

Una derivación es una lista de líneas. Cada línea es una premisa, una instancia de un **axioma** (se pulsa el axioma y se rellenan sus huecos con fórmulas) o se obtiene de otras líneas con una **regla**. Al principio todo se hace «a mano», solo con axiomas y modus ponens: cada derivación que completas desbloquea una **regla derivada** (∧I, ∧E, ∨E, ¬I, ∀E…) que el resto del juego tiene a un clic.

- **TD**, el teorema de la deducción, se usa con una subprueba: se supone A, se llega a B y se concluye A→B.
- **Nec** (necesitación) solo se aplica a teoremas. El juego sigue de qué premisas y supuestos depende cada línea, y los teoremas se marcan con el número en verde.
- **Gen** (generalización) exige que el nombre no figure en las premisas ni en los supuestos abiertos.
- Al final de cada mundo hay una máquina que decide la validez de argumentos propios (tablas, árboles, contramodelos de Kripke).

El mundo 6 es la excepción que enseña algo: en LP el modus ponens del condicional material no es válido, así que su cálculo de Hilbert no puede apoyarse en él.

## Desarrollo

```
node build.js    # genera index.html, manifest.webmanifest y sw.js (GitHub Pages y app instalable)
node test.js     # comprueba cada derivación, que cada axioma es válido en su semántica y que el motor rechaza pasos inválidos
```

Se edita `src/` (`engine.js` es el cálculo, `content.js` los mundos y sus derivaciones, `validity.js` las máquinas de validez, `ui.js` la interfaz) y se vuelve a ejecutar `node build.js`. `node mkico.js` regenera los iconos.
