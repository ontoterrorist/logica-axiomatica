/* Lógica Axiomática — contenido: mundos, teoría y retos.
   En los textos, {…} marca una fórmula. En las soluciones: ['H', f] supone, ['C'] cierra,
   [regla, líneas, resultado, fórmula extra, huecos del axioma]; ax(id, huecos, resultado) escribe el paso de un axioma. */
(function (root) {
'use strict';

/* Conjuntos de reglas de cada reto. Hay dos clases: los que se hacen «a mano», con axiomas y modus ponens,
   y los que ya cuentan con las reglas derivadas que el jugador demostró antes. */
const RS = {};
RS.h0 = ['A1', 'A2', 'MP'];
RS.h1 = ['R', 'A1', 'A2', 'MP', 'TD'];
RS.cAnd = ['R', 'A3', 'A4', 'A5', 'MP', 'TD'];
RS.cOr = ['R', 'A6', 'A7', 'A8', 'MP', 'TD'];
RS.cNeg = ['R', 'A1', 'A9', 'A10', 'A14', 'MP', 'TD'];
RS.cIff = ['R', 'A11', 'A12', 'A13', 'MP', 'TD'];
RS.and = ['R', '∧I', '∧E'];
RS.imp = [...RS.and, 'TD', 'MP'];
RS.or = [...RS.imp, '∨I', '∨E'];
RS.neg = [...RS.or, '¬I', '¬E', '⊥E', '¬¬E'];
RS.cl = [...RS.neg, '↔I', '↔E'];
RS.q0 = ['R', 'Q1', 'Q2', 'MP', 'TD'];
RS.fo1 = [...RS.neg, '∀E', '∃I'];
RS.fo2 = [...RS.fo1, 'Gen'];
RS.fo2q = [...RS.fo2, 'Q3'];
RS.cEx = [...RS.neg, '∃I', 'Gen', 'Q4'];
RS.fo = [...RS.fo2, '∃E'];
RS.k0 = [...RS.neg, 'K', 'Nec'];
RS.k1 = [...RS.k0, 'RK'];
RS.k = [...RS.k1, 'Mon', 'Def◇'];
RS.t = [...RS.k, 'T'];
RS.s4 = [...RS.t, '4'];
RS.s5 = [...RS.s4, '5'];
RS.qk = [...RS.fo, 'K', 'Nec', 'RK', 'Mon', 'Def◇', 'BF'];
RS.qt = [...RS.qk, 'T'];
RS.i0 = ['A10i', 'MP'];
RS.int = ['R', 'MP', 'TD', '∧I', '∧E', '∨I', '∨E', '¬I', '¬E', '⊥E'];
RS.intfo = [...RS.int, 'Gen', '∀E', '∃I', '∃E'];
RS.lp = ['R', '∧I', '∧E', '∨I', '∨E', 'DN', 'DeM', 'LEM'];
RS.lpq = [...RS.lp, 'Gen', '∀E', '∃I', '∃E', 'QN'];
RS.k4 = [...RS.cl, 'K', '4', 'Nec', 'RK', 'Mon'];      // lógica de la demostrabilidad: K4, sin el axioma T

/* numeración de Gödel usada en el Mundo 9: código de cada símbolo */
const GODEL = [['0', 1], ['S', 2], ['+', 3], ['×', 4], ['=', 5], ['(', 6], [')', 7], ['¬', 8], ['→', 9], ['∀', 10], ['x', 11]];
const GN = (title, mode, word, o) => Object.assign({ t: 'GN', title, mode, word }, o);

const T = (title, pages) => ({ t: 'T', title, pages });
const P = (title, prem, goal, rules, o) => Object.assign({ t: 'P', title, prem, goal, rules }, o);
const M = (title, logic, prem, goal, o) => Object.assign({ t: 'M', title, logic, prem, goal }, o);
const Q = (title, qs) => ({ t: 'Q', title, qs });
const TT = (title, cols, o) => Object.assign({ t: 'TT', title, cols }, o);
/* motor de validez al final de cada mundo: logic 'cl' | 'lp' | 'modal' | 'int'; sys = sistemas que se pueden elegir;
   cmp = lógica con la que se compara; goals = misiones; ex = ejemplos [premisas, conclusión, veredicto esperado, sistema] */
const V = (title, logic, o) => Object.assign({ t: 'V', title, logic }, o);
const fitch = rows => ({ k: 'fitch', rows });
const table = (head, rows) => ({ k: 'table', head, rows });
/* paso de una solución que usa un axioma: huecos = fórmulas que van en A, B, C… */
const ax = (id, huecos, out) => [id, [], out || null, null, huecos];

/* ============ MUNDO 0 · preliminares ============ */
const w0 = {
  k: 0, name: 'Campamento Base', logic: 'Preliminares: proposiciones, tablas y validez', badge: 'P',
  intro: 'Antes de salir de viaje conviene revisar el equipaje: qué es una proposición, cómo se combinan y cuándo un argumento es válido.',
  stages: [
    T('Qué es una proposición', [
      { say: '¡Bienvenido al campamento base! Soy <b>Minerva</b>. Antes de construir derivaciones hay que saber con qué material trabaja la lógica: las <b>proposiciones</b>.' },
      { say: 'Una proposición es lo que dice una oración declarativa: algo que puede ser <b>verdadero o falso</b>. Las preguntas, las órdenes y los deseos no afirman nada, así que no expresan proposiciones.', mood: 'neutral',
        fig: table(['Oración', '¿Expresa una proposición?'], [['«Llueve en Valdivia»', 'Sí'], ['«2 + 2 = 5»', 'Sí: es falsa, pero es una proposición'], ['«¿Llueve?»', 'No: es una pregunta'], ['«Cierra la puerta»', 'No: es una orden'], ['«Ojalá llueva»', 'No: es un deseo']]) },
      { say: 'La lógica clásica supone el principio de <b>bivalencia</b>: cada proposición tiene exactamente uno de dos valores de verdad, verdadero (V) o falso (F). Más adelante visitarás lógicas que ponen en duda ese supuesto.' },
      { say: 'Una proposición es <b>atómica</b> si no contiene otra proposición como parte: «llueve». Es <b>compuesta</b> si se arma con otras: «llueve y hace frío». A las atómicas las abreviamos con letras: {P}, {Q}, {R}.' }
    ]),
    Q('¿Proposición o no?', [
      { q: '¿Cuál de estas oraciones expresa una proposición?', opts: ['«¿Qué hora es?»', '«La Tierra gira alrededor del Sol»', '«Pásame la sal»'], ok: 1,
        why: 'Es la única que afirma algo que puede ser verdadero o falso. Las otras son una pregunta y una petición.' },
      { q: '«La Luna es de queso». ¿Expresa una proposición?', opts: ['No, porque es falsa', 'Sí: es falsa, pero tiene valor de verdad', 'Solo si alguien se la cree'], ok: 1,
        why: 'Ser proposición no exige ser verdadera. Basta con que tenga sentido preguntar si lo es.' },
      { q: '¿Cuál de estas proposiciones es atómica?', opts: ['«Llueve y hace frío»', '«No llueve»', '«Llueve»'], ok: 2,
        why: 'Las otras dos contienen la proposición «llueve» como parte, combinada con «y» o con «no».' },
      { q: '«Ojalá apruebe el examen» es…', opts: ['un deseo: no expresa una proposición', 'una proposición verdadera', 'una proposición falsa'], ok: 0,
        why: 'Quien la dice no afirma que vaya a aprobar. No hay nada que evaluar como verdadero o falso.' }
    ]),
    T('Contenido proposicional', [
      { say: 'No confundas la oración con la proposición. «Llueve», «Está lloviendo» e «It is raining» son tres oraciones distintas, pero dicen lo mismo. Eso que tienen en común es su <b>contenido proposicional</b>.', mood: 'neutral' },
      { say: 'El contenido tampoco es lo mismo que la <b>fuerza</b> con que se usa. Estas tres oraciones comparten un contenido, pero con una se afirma, con otra se pregunta y con otra se ordena.', mood: 'neutral',
        fig: table(['Oración', 'Fuerza', 'Contenido'], [['«Cierras la puerta»', 'afirmación', 'que cierras la puerta'], ['«¿Cierras la puerta?»', 'pregunta', 'que cierras la puerta'], ['«¡Cierra la puerta!»', 'orden', 'que cierras la puerta']]) },
      { say: 'Al revés, una misma oración puede expresar proposiciones distintas según quién la diga y cuándo. «Yo tengo hambre» dice una cosa en boca de Ana y otra en boca de Luis. A la lógica le interesa el contenido, no las palabras.' },
      { say: 'Entonces, ¿cómo se identifica un contenido? Por sus <b>condiciones de verdad</b>: conocer el contenido de una proposición es saber en qué situaciones sería verdadera y en cuáles falsa. Las tablas de verdad harán precisa esta idea.' }
    ]),
    Q('Lo mismo con otras palabras', [
      { q: '¿Qué par de oraciones afirma lo mismo?', opts: ['«Ana ama a Luis» y «Luis ama a Ana»', '«Ana ama a Luis» y «Luis es amado por Ana»', '«Ana ama a Luis» y «Ana no odia a Luis»'], ok: 1,
        why: 'La voz activa y la pasiva cambian las palabras, no el contenido: son verdaderas exactamente en las mismas situaciones.' },
      { q: '«La ventana está abierta» y «¿Está abierta la ventana?» comparten…', opts: ['la fuerza, pero no el contenido', 'el contenido, pero no la fuerza', 'ni una cosa ni la otra'], ok: 1,
        why: 'El contenido es el mismo: que la ventana está abierta. Con una se afirma y con la otra se pregunta.' },
      { q: 'Pedro dice «yo soy chileno» y Kenji dice «yo soy chileno». Tenemos…', opts: ['la misma oración y la misma proposición', 'la misma oración y dos proposiciones distintas', 'dos oraciones y la misma proposición'], ok: 1,
        why: 'Una habla de Pedro y la otra de Kenji: pueden tener valores de verdad distintos, así que son proposiciones distintas.' }
    ]),
    T('Conectores', [
      { say: 'Las proposiciones compuestas se forman con <b>conectores</b>. Los de la lógica clásica son <b>veritativo-funcionales</b>: el valor de la compuesta depende solo del valor de sus partes.',
        fig: table(['Conector', 'Nombre', 'Se lee', 'Ejemplo'], [['{¬}', 'negación', 'no', '{¬P}'], ['{∧}', 'conjunción', 'y', '{P∧Q}'], ['{∨}', 'disyunción', 'o', '{P∨Q}'], ['{→}', 'condicional', 'si… entonces', '{P→Q}'], ['{↔}', 'bicondicional', 'si y solo si', '{P↔Q}']]) },
      { say: '<b>Formalizar</b> es pasar del castellano a fórmulas. Primero eliges una letra para cada proposición atómica; luego buscas el conector principal. «Si llueve y no llevo paraguas, me mojo» queda {(P∧¬Q)→R}.',
        fig: table(['Letra', 'Proposición'], [['{P}', 'llueve'], ['{Q}', 'llevo paraguas'], ['{R}', 'me mojo']]) },
      { say: 'Los paréntesis importan. {P∧(Q∨R)} y {(P∧Q)∨R} no dicen lo mismo: en la primera {P} tiene que darse sí o sí; en la segunda basta con {R}.' },
      { say: 'Algunas pistas de traducción. En {P→Q}, {P} es el <b>antecedente</b> y {Q} el <b>consecuente</b>.',
        fig: table(['En castellano', 'Fórmula'], [['P pero Q', '{P∧Q}'], ['ni P ni Q', '{¬P∧¬Q}'], ['P si Q', '{Q→P}'], ['P solo si Q', '{P→Q}'], ['P a menos que Q', '{¬Q→P}']]) }
    ]),
    Q('Formalizar', [
      { q: 'Con {P}: «llueve» y {Q}: «hace frío». ¿Cómo se formaliza «Llueve pero no hace frío»?', opts: ['{P∧¬Q}', '{¬(P∧Q)}', '{P∨¬Q}'], ok: 0,
        why: '«Pero» es una conjunción. La negación afecta solo a «hace frío».' },
      { q: 'Añadimos {R}: «salgo». «Si llueve o hace frío, no salgo» es…', opts: ['{P∨(Q→¬R)}', '{(P∨Q)→¬R}', '{(P∧Q)→¬R}'], ok: 1,
        why: 'El conector principal es el condicional: todo «llueve o hace frío» es el antecedente.' },
      { q: '«Salgo solo si no llueve» es…', opts: ['{¬P→R}', '{R→¬P}', '{R↔¬P}'], ok: 1,
        why: '«Solo si» introduce una condición necesaria: si salgo, es que no llueve. No dice que siempre que no llueva vaya a salir.' },
      { q: '«Ni llueve ni hace frío» es…', opts: ['{¬P∧¬Q}', '{¬(P∧Q)}', '{¬P∨¬Q}'], ok: 0,
        why: 'Niega las dos cosas. {¬(P∧Q)} solo dice que no se dan ambas a la vez.' }
    ]),
    T('Tablas de verdad', [
      { say: 'Una <b>valuación</b> le asigna V o F a cada letra. La tabla de verdad de un conector dice qué valor tiene la compuesta en cada caso. La negación invierte el valor.',
        fig: [table(['{A}', '{¬A}'], [['V', 'F'], ['F', 'V']]), table(['{A}', '{B}', '{A∧B}', '{A∨B}', '{A→B}', '{A↔B}'], [['V', 'V', 'V', 'V', 'V', 'V'], ['V', 'F', 'F', 'V', 'F', 'F'], ['F', 'V', 'F', 'V', 'V', 'F'], ['F', 'F', 'F', 'F', 'V', 'V']])] },
      { say: 'Tres cosas que conviene recordar. La conjunción solo es verdadera si lo son las dos partes. La disyunción es <b>inclusiva</b>: solo es falsa si las dos partes lo son. Y el condicional solo es falso cuando el antecedente es verdadero y el consecuente falso.' },
      { say: 'Para una fórmula compuesta haces una fila por cada valuación: con dos letras son 4 filas, con tres son 8. Se calcula de dentro hacia fuera: primero las partes y al final el conector principal.',
        fig: table(['{P}', '{Q}', '{¬P}', '{¬P∨Q}'], [['V', 'V', 'F', 'V'], ['V', 'F', 'F', 'F'], ['F', 'V', 'V', 'V'], ['F', 'F', 'V', 'V']]) },
      { say: 'En los retos de tabla, toca cada casilla para poner V y tócala otra vez para cambiarla a F. Cuando hayas llenado todas las columnas, pulsa <b>Comprobar</b>.' }
    ]),
    TT('Tu primera tabla', ['P∧Q', '¬(P∧Q)'], {
      intro: 'Llena primero la columna de {P∧Q} y úsala para calcular {¬(P∧Q)}.',
      outro: 'La negación invierte la columna: {¬(P∧Q)} solo es falsa cuando {P} y {Q} son verdaderas.' }),
    TT('El condicional y su contrapuesta', ['P→Q', '¬Q→¬P'], {
      intro: 'Calcula las dos columnas con cuidado y compáralas al terminar.',
      outro: 'Las dos columnas son idénticas: {P→Q} y {¬Q→¬P} son equivalentes. Dicen lo mismo con otras palabras.' }),
    TT('Tres letras, ocho filas', ['Q∨R', 'P∧(Q∨R)'], {
      intro: 'Con tres letras hay ocho valuaciones. Ve por partes: primero {Q∨R}.',
      outro: '{P∧(Q∨R)} es verdadera en tres de las ocho filas: hace falta {P} y al menos una de las otras dos.' }),
    T('Contenido, equivalencia y tautologías', [
      { say: 'Mira la columna final de una tabla. Si todo son V, la fórmula es una <b>tautología</b>: es verdadera pase lo que pase. Si todo son F, es una <b>contradicción</b>. Si hay de las dos, es una <b>contingencia</b>.', mood: 'neutral',
        fig: table(['{P}', '{P∨¬P}', '{P∧¬P}'], [['V', 'V', 'F'], ['F', 'V', 'F']]) },
      { say: 'Ahora podemos precisar qué es el contenido: son las condiciones de verdad, es decir, la columna de la tabla. Dos fórmulas con la misma columna son <b>lógicamente equivalentes</b>: tienen el mismo contenido dicho de dos maneras. Ya lo viste con {P→Q} y {¬Q→¬P}.', mood: 'neutral' },
      { say: 'Cuantas más situaciones excluye una proposición, más dice. {P∧Q} dice más que {P}, porque descarta más filas. Una tautología no descarta ninguna: no informa de nada. Una contradicción las descarta todas: no puede ser verdadera.' }
    ]),
    TT('Siempre verdadera', ['P∧Q', '(P∧Q)→P'], {
      intro: 'Calcula la tabla de {(P∧Q)→P} y fíjate en su columna.',
      outro: 'Todo V: es una tautología. No puede ser falsa porque, si {P∧Q} es verdadera, {P} también lo es.' }),
    Q('Clasifica', [
      { q: '{P∧¬P} es una…', opts: ['tautología', 'contradicción', 'contingencia'], ok: 1,
        why: 'Sea cual sea el valor de {P}, una de las dos partes es falsa, así que la conjunción siempre lo es.' },
      { q: '{P→P} es una…', opts: ['tautología', 'contradicción', 'contingencia'], ok: 0,
        why: 'Un condicional solo es falso con antecedente verdadero y consecuente falso, y aquí son la misma proposición.' },
      { q: '¿Cuál tiene el mismo contenido que {¬(P∧Q)}?', opts: ['{¬P∧¬Q}', '{¬P∨¬Q}', '{P∨Q}'], ok: 1,
        why: 'Negar que se den las dos es decir que al menos una falla. Es una de las leyes de De Morgan; puedes comprobarla con una tabla.' },
      { q: '¿Cuál de estas dice más, es decir, excluye más situaciones?', opts: ['{P∨Q}', '{P}', '{P∧Q}'], ok: 2,
        why: '{P∧Q} solo es verdadera en una fila de cuatro. {P} lo es en dos y {P∨Q} en tres.' }
    ]),
    T('Consistencia', [
      { say: 'Un conjunto de proposiciones es <b>consistente</b> si todas pueden ser verdaderas a la vez: hay al menos una valuación que las hace verdaderas a todas. Si no hay ninguna, es <b>inconsistente</b>.', mood: 'neutral' },
      { say: 'En una tabla conjunta buscas una fila donde todas valgan V. Aquí no hay ninguna: {P}, {P→Q} y {¬Q} forman un conjunto inconsistente.',
        fig: table(['{P}', '{Q}', '{P→Q}', '{¬Q}', '¿Las tres V?'], [['V', 'V', 'V', 'F', 'no'], ['V', 'F', 'F', 'V', 'no'], ['F', 'V', 'V', 'F', 'no'], ['F', 'F', 'V', 'V', 'no']]) },
      { say: 'Consistente no significa verdadero. Significa solo que las proposiciones no se estorban entre sí: «llueve» y «hace frío» son consistentes aunque hoy haga sol. Una contradicción, en cambio, es inconsistente ella sola.' },
      { say: 'En los dos retos siguientes tienes que mostrar que un conjunto es consistente: encuentra una valuación que haga verdaderas todas sus proposiciones.' }
    ]),
    M('Tres que conviven', 'CL', ['P∨Q', '¬P', 'Q→R'], null, { mode: 'sat',
      intro: 'Busca una valuación que haga verdaderas las tres proposiciones a la vez.',
      outro: 'Con {P} falsa y {Q} y {R} verdaderas, las tres son verdaderas. Una sola valuación basta para que el conjunto sea consistente.' }),
    M('Con un poco de maña', 'CL', ['P→Q', '¬Q', 'P∨R'], null, { mode: 'sat',
      intro: 'Este conjunto deja menos margen. Empieza por la proposición que solo puede ser verdadera de una manera.',
      outro: '{¬Q} obliga a que {Q} sea falsa; entonces {P→Q} obliga a que {P} sea falsa, y {P∨R} a que {R} sea verdadera.' }),
    Q('¿Consistente o no?', [
      { q: '¿Es consistente el conjunto formado por {P}, {P→Q} y {¬Q}?', opts: ['Sí', 'No'], ok: 1,
        why: 'Si {P} y {P→Q} son verdaderas, {Q} tiene que serlo, y entonces {¬Q} es falsa.' },
      { q: '¿Y el formado por {P→Q} y {¬P}?', opts: ['Sí', 'No'], ok: 0,
        why: 'Con {P} falsa las dos son verdaderas, valga {Q} lo que valga.' },
      { q: '¿Y el formado por {P∨Q}, {¬P} y {¬Q}?', opts: ['Sí', 'No'], ok: 1,
        why: 'Las dos negaciones exigen que {P} y {Q} sean falsas, y entonces {P∨Q} es falsa.' },
      { q: 'Si un conjunto es consistente, ¿son verdaderas todas sus proposiciones?', opts: ['Sí, siempre', 'No: solo pueden serlo a la vez', 'Depende de cuántas sean'], ok: 1,
        why: 'La consistencia habla de posibilidad conjunta, no de verdad de hecho.' }
    ]),
    T('Validez', [
      { say: 'Un <b>argumento</b> tiene premisas y una conclusión. Es <b>válido</b> cuando es imposible que las premisas sean verdaderas y la conclusión falsa: ninguna valuación lo consigue. En el juego lo verás escrito así: {P→Q, P ⊢ Q}.', mood: 'neutral' },
      { say: 'Con una tabla: marca las filas donde todas las premisas son V y mira la conclusión en esas filas. En este argumento solo hay una, la primera, y en ella la conclusión es V. Es válido.',
        fig: table(['{P}', '{Q}', 'Premisa {P→Q}', 'Premisa {P}', 'Conclusión {Q}'], [['V', 'V', 'V', 'V', 'V'], ['V', 'F', 'F', 'V', 'F'], ['F', 'V', 'V', 'F', 'V'], ['F', 'F', 'V', 'F', 'F']]) },
      { say: 'Válido no quiere decir que las premisas sean verdaderas. «Si la Luna es de queso, es comestible; la Luna es de queso; luego es comestible» es válido. La validez depende de la forma. Un argumento válido con premisas verdaderas se llama <b>sólido</b>.' },
      { say: 'Validez y consistencia son dos caras de lo mismo: un argumento es válido exactamente cuando sus premisas, junto con la <b>negación</b> de la conclusión, forman un conjunto inconsistente. Un <b>contraejemplo</b> es una valuación que muestra lo contrario.', mood: 'neutral' },
      { say: 'Las tablas siempre funcionan, pero crecen muy rápido: con diez letras ya son 1024 filas. En el Mundo 1 aprenderás otro método, el <b>cálculo axiomático</b> de Hilbert, que llega a la conclusión paso a paso.', mood: 'neutral' }
    ]),
    TT('Modus tollens en tabla', ['P→Q', '¬Q', '¬P'], {
      intro: 'Las dos primeras columnas son las premisas y la tercera la conclusión. Llénalas y busca las filas con premisas verdaderas.',
      outro: 'Solo en la última fila son verdaderas las dos premisas, y ahí la conclusión también lo es. El argumento {P→Q, ¬Q ⊢ ¬P} es válido.' }),
    M('Negar el antecedente', 'CL', ['P→Q', '¬P'], '¬Q', {
      intro: 'Este argumento parece razonable y no lo es. Encuentra el contraejemplo: premisas verdaderas y conclusión falsa.',
      outro: 'Con {P} falsa y {Q} verdadera, las premisas son verdaderas y la conclusión falsa. «Negar el antecedente» es una falacia.' }),
    Q('Validez', [
      { q: 'Un argumento válido tiene una conclusión falsa. ¿Qué se sigue?', opts: ['Eso es imposible', 'Al menos una premisa es falsa', 'En realidad era inválido'], ok: 1,
        why: 'Si todas las premisas fueran verdaderas, la conclusión tendría que serlo. Como no lo es, alguna premisa falla.' },
      { q: '¿Es válido {P→Q, Q→R ⊢ P→R}?', opts: ['Sí', 'No'], ok: 0,
        why: 'Para que la conclusión fuera falsa haría falta {P} verdadera y {R} falsa, y entonces alguna premisa sería falsa.' },
      { q: 'Un argumento es válido exactamente cuando sus premisas forman un conjunto inconsistente junto con…', opts: ['la conclusión', 'la negación de la conclusión', 'una tautología'], ok: 1,
        why: 'Decir que no pueden darse premisas verdaderas y conclusión falsa es decir que las premisas y la negación de la conclusión no pueden ser verdaderas a la vez.' },
      { q: '¿Puede un argumento válido tener premisas falsas y conclusión verdadera?', opts: ['Sí', 'No'], ok: 0,
        why: '«Todos los peces vuelan; las águilas son peces; luego las águilas vuelan». La validez solo prohíbe premisas verdaderas con conclusión falsa.' }
    ]),
    V('La máquina de tablas', 'cl', { table: true, syms: '¬∧∨→↔', goals: ['valid', 'invalid', 'own'],
      intro: 'Al final del campamento hay una máquina que hace tablas de verdad sola. Escribe las premisas y la conclusión y pulsa <b>Analizar</b>: marcará las filas con premisas verdaderas y, en rojo, las que refutan el argumento.',
      outro: 'Una tabla siempre termina. Por eso la validez en lógica proposicional es <b>decidible</b>: basta revisar las 2ⁿ filas.',
      ex: [[['P→Q', 'P'], 'Q', 'valid'], [['P→Q', 'Q'], 'P', 'invalid'], [['P→Q', '¬Q'], '¬P', 'valid'], [['P→Q', '¬P'], '¬Q', 'invalid'], [['P∨Q', '¬P'], 'Q', 'valid'], [['P'], 'P∧Q', 'invalid']] })
  ]
};

/* ============ MUNDO 1 · proposicional clásica ============ */
const w1 = {
  k: 1, name: 'Pradera Proposicional', logic: 'Lógica proposicional clásica', badge: '∧',
  intro: 'Aquí se aprende el oficio: los axiomas de cada conectiva, el modus ponens y cómo se arma una derivación al modo de Hilbert.',
  stages: [
    T('Qué es un cálculo axiomático', [
      { say: '¡Hola! Soy <b>Minerva</b>. Vamos a recorrer diez mundos, y en cada uno aprenderás una lógica distinta. Pero no las aprenderás con montones de reglas y subpruebas, sino a la manera de <b>David Hilbert</b>: con axiomas.' },
      { say: 'Un <b>cálculo axiomático</b> tiene tres piezas: un lenguaje, unos <b>axiomas</b> que se aceptan sin prueba, y unas <b>reglas de inferencia</b> para sacar fórmulas de otras. En la lógica clásica la única regla es el <b>modus ponens</b>.',
        fig: table(['Pieza', 'Qué es', 'En este mundo'], [['Lenguaje', 'las fórmulas bien formadas', '{¬}  {∧}  {∨}  {→}  {↔}  {⊥}'], ['Axiomas', 'fórmulas que valen sin prueba', 'esquemas {A1}, {A2}, {A3}…'], ['Regla', 'cómo obtener una fórmula de otras', '{MP}: de {A→B} y {A}, {B}']]) },
      { say: 'Los axiomas son <b>esquemas</b>. {A→(B→A)} no es una fórmula sino una receta: en ella, {A} y {B} se reemplazan por fórmulas cualesquiera. Cada resultado es una <b>instancia</b> del axioma.',
        fig: table(['Receta', 'Instancia', 'Cambiando…'], [['{A→(B→A)}', '{P→(Q→P)}', '{A} por {P}, {B} por {Q}'], ['{A→(B→A)}', '{P→(P→P)}', '{A} y {B} por {P}'], ['{A→(B→A)}', '{(P∧Q)→(R→(P∧Q))}', '{A} por {P∧Q}, {B} por {R}']]) },
      { say: 'Una <b>derivación</b> es una lista numerada. Cada línea es una premisa, una instancia de un axioma, o sale por {MP} de dos líneas anteriores. La última línea queda demostrada. Sin cajas ni subpruebas: solo axiomas y modus ponens.',
        fig: fitch([[1, 0, 'P', 'Premisa', 'p'], [2, 0, 'P→(Q→P)', 'A1'], [3, 0, 'Q→P', 'MP 2, 1']]) },
      { say: 'Si la derivación no usa premisas, su última línea es un <b>teorema</b>: se escribe {⊢ A}. Con premisas, {Γ ⊢ A} se lee «A se deduce de Γ».' },
      { say: 'En el juego: pulsa un axioma, rellena sus huecos con fórmulas y se añade la línea. Para {MP}, toca las dos líneas que quieres usar y pulsa la regla. Ganas cuando la conclusión aparece en la columna principal.' }
    ]),
    T('El condicional: A1, A2 y MP', [
      { say: 'El condicional se gobierna con dos axiomas y la regla. El primero dice que una verdad se puede añadir como condición de lo que sea: si ya tienes {A}, entonces {B→A}.',
        fig: table(['Nombre', 'Esquema', 'Idea'], [['{A1}', '{A→(B→A)}', 'una premisa de sobra no estorba'], ['{A2}', '{(A→(B→C))→((A→B)→(A→C))}', 'el condicional se reparte'], ['{MP}', 'de {A→B} y {A}, {B}', 'modus ponens']]) },
      { say: '{A2} es el más difícil de leer. Dice: si {A} lleva a {B→C}, y {A} lleva a {B}, entonces {A} lleva a {C}. Su trabajo se ve mejor en la práctica: lo necesitarás para demostrar algo tan simple como {P→P}.' },
      { say: 'Los huecos de un axioma se rellenan con fórmulas completas, no solo con letras. Con {A2} pondrás {P→P} en el hueco de {B}.' }
    ]),
    P('Una premisa de sobra', ['P'], 'Q→P', 'h0', { sys: 'H',
      intro: 'Tienes {P}. Con un axioma y un modus ponens llegas a {Q→P}.',
      hints: ['Pulsa {A1} y rellena los huecos: {A} es {P} y {B} es {Q}. Obtienes {P→(Q→P)}.', 'Selecciona esa línea y la premisa {P} y pulsa {MP}.'],
      sol: [ax('A1', { A: 'P', B: 'Q' }), ['MP', [2, 1]]] }),
    P('Modus ponens en cadena', ['P→Q', 'Q→R', 'P'], 'R', 'h0', { sys: 'H',
      intro: 'Dos pasos de {MP} seguidos, sin axiomas.',
      hints: ['Selecciona las líneas 1 y 3 y pulsa {MP} para obtener {Q}.', 'Ahora combina {Q→R} con la {Q} que acabas de obtener.'],
      sol: [['MP', [1, 3]], ['MP', [2, 4]]] }),
    P('La identidad', [], 'P→P', 'h0', { sys: 'H',
      intro: 'El primer teorema que se prueba en cualquier libro de lógica. Parece trivial, pero con estos axiomas hacen falta cinco líneas.',
      hints: ['Empieza por {A2} con {A} = {P}, {B} = {P→P} y {C} = {P}.', 'Usa {A1} con {A} = {P} y {B} = {P→P} para obtener {P→((P→P)→P)}, que es justo el antecedente de la línea 1. Aplica {MP}.', 'Te queda {(P→(P→P))→(P→P)}. Obtén {P→(P→P)} con {A1} ({A} y {B} son {P}) y cierra con {MP}.'],
      sol: [ax('A2', { A: 'P', B: 'P→P', C: 'P' }), ax('A1', { A: 'P', B: 'P→P' }), ['MP', [1, 2]], ax('A1', { A: 'P', B: 'P' }), ['MP', [3, 4]]] }),
    T('El teorema de la deducción', [
      { say: 'Demostrar {P→P} costó cinco líneas. Probar así un silogismo entero sería una pesadilla. Por eso se usa un resultado clave de Herbrand y Tarski: el <b>teorema de la deducción</b>.' },
      { say: '<b>TD</b>: si, <i>suponiendo {A}</i> (y lo que ya tenías), se deriva {B}, entonces sin ese supuesto se deriva {A→B}. Es un <i>metateorema</i>: no sale de los axiomas de golpe, pero se demuestra por inducción sobre la longitud de la derivación, con ayuda de {A1} y {A2}.',
        fig: fitch([['i', 1, 'A', 'Supuesto', 'h'], ['', 1, '⋮', ''], ['j', 1, 'B', ''], ['', 0, 'A→B', 'TD i–j']]) },
      { say: 'Por eso {TD} es una <b>regla derivada</b>: sin ella todo se podría hacer igual, solo que en muchas más líneas. En el juego: pulsa <b>Suponer</b> y elige la fórmula; trabaja dentro con los axiomas y {MP}; cuando llegues a {B}, pulsa {TD}.' },
      { say: 'El supuesto solo vale dentro de su subprueba. Cuando se cierra, sus líneas dejan de estar disponibles: lo que probaste ahí dependía de suponer {A}. La regla <b>R</b> repite una línea disponible.' },
      { say: 'Así se ve la identidad con {TD}: tres líneas en vez de cinco.',
        fig: fitch([[1, 1, 'P', 'Supuesto', 'h'], [2, 0, 'P→P', 'TD 1–1']]) }
    ]),
    P('Silogismo hipotético', ['P→Q', 'Q→R'], 'P→R', 'h1', { sys: 'H',
      intro: 'La conclusión es un condicional. Para probarlo, supón su antecedente.',
      hints: ['Pulsa <b>Suponer</b> y elige {P}.', 'Dentro de la subprueba, usa {MP} dos veces hasta llegar a {R}.', 'Con {R} como última línea de la subprueba, pulsa {TD}.'],
      sol: [['H', 'P'], ['MP', [1, 3]], ['MP', [2, 4]], ['TD']] }),
    P('Permutación', ['P→(Q→R)'], 'Q→(P→R)', 'h1', { sys: 'H',
      intro: 'Dos supuestos anidados: se pueden intercambiar las condiciones de un condicional.',
      hints: ['Supón {Q} y, dentro, supón {P}.', 'Con {MP} sobre la premisa y {P} obtienes {Q→R}; otro {MP} con {Q} te da {R}.', 'Pulsa {TD} dos veces: primero se cierra la subprueba de {P}, luego la de {Q}.'],
      sol: [['H', 'Q'], ['H', 'P'], ['MP', [1, 3]], ['MP', [4, 2]], ['TD'], ['TD']] }),
    T('Conjunción: A3, A4 y A5', [
      { say: 'La conjunción tiene tres axiomas: uno para construirla y dos para desmontarla.',
        fig: table(['Nombre', 'Esquema', 'Idea'], [['{A3}', '{A→(B→(A∧B))}', 'dos verdades hacen una conjunción'], ['{A4}', '{(A∧B)→A}', 'me quedo con la primera'], ['{A5}', '{(A∧B)→B}', 'me quedo con la segunda']]) },
      { say: 'Con {A3} y dos {MP} se pasa de {A} y {B} a {A∧B}. Con {A4} o {A5} y un {MP}, de {A∧B} a una de sus partes. Esas dos operaciones se necesitan tanto que se les da nombre propio: <b>∧I</b> (introducción) y <b>∧E</b> (eliminación).' },
      { say: 'Primero las construirás a mano, solo con axiomas. Cuando termines, quedarán guardadas como <b>reglas derivadas</b> y el resto del juego las tendrá a un clic.' }
    ]),
    P('Construye ∧I', ['P', 'Q'], 'P∧Q', 'cAnd', { sys: 'H',
      intro: 'De {P} y {Q}, a {P∧Q} con {A3}. Es la regla ∧I desmontada.',
      hints: ['Pulsa {A3} con {A} = {P} y {B} = {Q}: {P→(Q→(P∧Q))}.', 'Un {MP} con {P} te da {Q→(P∧Q)}.', 'Otro {MP} con {Q} termina.'],
      sol: [ax('A3', { A: 'P', B: 'Q' }), ['MP', [3, 1]], ['MP', [4, 2]]] }),
    P('Dar la vuelta a mano', ['P∧Q'], 'Q∧P', 'cAnd', { sys: 'H',
      intro: 'Desmonta la premisa con {A4} y {A5}; vuelve a montarla al revés con {A3}. Con esto quedan demostradas {∧I} y {∧E}.',
      hints: ['{A5} con {A} = {P} y {B} = {Q} y un {MP} con la premisa: sacas {Q}. Con {A4}, sacas {P}.', 'Ahora {A3} con {A} = {Q} y {B} = {P}: {Q→(P→(Q∧P))}.', 'Dos {MP}: primero con {Q}, después con {P}.'],
      sol: [ax('A5', { A: 'P', B: 'Q' }), ['MP', [2, 1]], ax('A4', { A: 'P', B: 'Q' }), ['MP', [4, 1]], ax('A3', { A: 'Q', B: 'P' }), ['MP', [6, 3]], ['MP', [7, 5]]] }),
    P('Desmontar y montar', ['P∧(Q∧R)'], 'R∧P', 'and', {
      intro: 'Ya tienes {∧I} y {∧E} como reglas. Primero desmonta la premisa con {∧E}; después monta la conclusión con {∧I}.',
      hints: ['Usa {∧E} sobre la línea 1 dos veces: una para obtener {P} y otra para obtener {Q∧R}.', 'Saca {R} de {Q∧R} con otro {∧E}.', 'Selecciona {R} y {P} y pulsa {∧I}.'],
      sol: [['∧E', [1], 'P'], ['∧E', [1], 'Q∧R'], ['∧E', [3], 'R'], ['∧I', [4, 2], 'R∧P']] }),
    P('Exportación', ['(P∧Q)→R'], 'P→(Q→R)', 'imp', {
      intro: 'Dos supuestos anidados y un poco de todo lo anterior.',
      hints: ['Supón {P} y después, dentro, supón {Q}.', 'Une {P} y {Q} con {∧I}: así tienes el antecedente de la premisa.', 'Aplica {MP} para obtener {R} y cierra las dos subpruebas con {TD}.'],
      sol: [['H', 'P'], ['H', 'Q'], ['∧I', [2, 3], 'P∧Q'], ['MP', [1, 4]], ['TD'], ['TD']] }),
    T('Disyunción: A6, A7 y A8', [
      { say: '{A∨B} dice que al menos una de las dos es verdadera. Introducirla es fácil: dos axiomas, uno por cada lado.',
        fig: table(['Nombre', 'Esquema', 'Idea'], [['{A6}', '{A→(A∨B)}', 'de {A}, {A∨B}'], ['{A7}', '{B→(A∨B)}', 'de {B}, {A∨B}'], ['{A8}', '{(A→C)→((B→C)→((A∨B)→C))}', 'prueba por casos']]) },
      { say: 'Usarla es más delicado, porque no sabes cuál de las dos se da. {A8} lo resuelve: si {A} lleva a {C} y {B} también lleva a {C}, entonces {A∨B} lleva a {C}.' },
      { say: 'Con {A6} y {A7} se obtiene la regla <b>∨I</b>. Con {A8} y {TD}, la regla <b>∨E</b>, que se usa con una subprueba por caso. En el juego: supón el primer caso y llega a {C}; pulsa <b>Cerrar sub.</b>; supón el segundo caso y llega otra vez a {C}; entonces pulsa {∨E}.',
        fig: fitch([['m', 0, 'A∨B', ''], ['i', 1, 'A', 'Supuesto', 'h'], ['j', 1, 'C', ''], ['k', 1, 'B', 'Supuesto', 'h'], ['l', 1, 'C', ''], ['', 0, 'C', '∨E m, i–j, k–l']]) }
    ]),
    P('Construye ∨I', ['P'], 'Q∨P', 'cOr', { sys: 'H',
      intro: 'Con {A7} se pone {P} al lado derecho de la disyunción.',
      hints: ['{A7} tiene la forma {B→(A∨B)}. Rellena {A} con {Q} y {B} con {P}.', 'Un {MP} con la premisa termina.'],
      sol: [ax('A7', { A: 'Q', B: 'P' }), ['MP', [2, 1]]] }),
    P('Construye ∨E', ['P∨Q', 'P→R', 'Q→R'], 'R', 'cOr', { sys: 'H',
      intro: 'El dilema, a mano. Con {A8} y tres {MP} se razona por casos.',
      hints: ['Pulsa {A8} con {A} = {P}, {B} = {Q} y {C} = {R}.', 'Un {MP} con {P→R} te da {(Q→R)→((P∨Q)→R)}. Otro con {Q→R}, {(P∨Q)→R}.', 'Un último {MP} con la disyunción {P∨Q}.'],
      sol: [ax('A8', { A: 'P', B: 'Q', C: 'R' }), ['MP', [4, 2]], ['MP', [5, 3]], ['MP', [6, 1]]] }),
    P('Conmutar', ['P∨Q'], 'Q∨P', 'or', {
      intro: 'Ya tienes {∨I} y {∨E}. Prueba por casos: en cada caso tienes que llegar a {Q∨P}.',
      hints: ['Supón {P}. Con {∨I} obtén {Q∨P} y pulsa <b>Cerrar sub.</b>', 'Supón {Q} y llega otra vez a {Q∨P} con {∨I}.', 'Con la segunda subprueba todavía abierta, pulsa {∨E}.'],
      sol: [['H', 'P'], ['∨I', [2], 'Q∨P', 'Q'], ['C'], ['H', 'Q'], ['∨I', [4], 'Q∨P', 'P'], ['∨E', [1]]] }),
    P('Distribuir', ['P∧(Q∨R)'], '(P∧Q)∨(P∧R)', 'or', {
      intro: 'Desmonta la conjunción y razona por casos sobre la disyunción que hay dentro.',
      hints: ['Con {∧E} obtén {P} y {Q∨R} por separado.', 'Caso {Q}: forma {P∧Q} y pásala a la conclusión con {∨I}. Cierra la subprueba.', 'Caso {R}: forma {P∧R}, aplica {∨I} y termina con {∨E}.'],
      sol: [['∧E', [1], 'P'], ['∧E', [1], 'Q∨R'], ['H', 'Q'], ['∧I', [2, 4], 'P∧Q'], ['∨I', [5], '(P∧Q)∨(P∧R)', 'P∧R'], ['C'],
        ['H', 'R'], ['∧I', [2, 7], 'P∧R'], ['∨I', [8], '(P∧Q)∨(P∧R)', 'P∧Q'], ['∨E', [3]]] }),
    T('Negación y absurdo: A9, A10 y A14', [
      { say: 'La negación necesita dos axiomas, y el absurdo {⊥} uno más. {⊥} es una fórmula que nunca es verdadera.',
        fig: table(['Nombre', 'Esquema', 'Idea'], [['{A9}', '{(A→B)→((A→¬B)→¬A)}', 'reducción al absurdo'], ['{A10}', '{¬¬A→A}', 'doble negación (solo clásica)'], ['{A14}', '{¬⊥}', 'el absurdo es falso']]) },
      { say: '{A10} es el axioma que hace <i>clásica</i> a esta lógica. Hay lógicas, como la intuicionista del Mundo 5, que lo cambian por otro. Con él se prueban el tercero excluido, {P∨¬P}, y las leyes de De Morgan.' },
      { say: 'Con estos axiomas se demuestra una de las leyes más famosas: la <b>explosión</b>. De {A} y {¬A} se sigue cualquier fórmula {B}. Es la parte más larga del mundo; respira hondo.' },
      { say: 'De la explosión salen dos reglas: <b>¬E</b> (de {A} y {¬A}, {⊥}) y <b>⊥E</b> (de {⊥}, cualquier cosa, usando {A14}). Con {A9} y {A14} sale <b>¬I</b>: si suponer {A} lleva a {⊥}, entonces {¬A}. Y con {A10}, la regla <b>¬¬E</b>.' }
    ]),
    P('Explosión', ['P', '¬P'], 'Q', 'cNeg', { sys: 'H',
      intro: 'De una contradicción se sigue todo. Es el truco más largo del libro: usa {A1} dos veces, {A9} y {A10}.',
      hints: ['Obtén {¬Q→P} y {¬Q→¬P} con {A1} y {MP}: {A1} da {P→(¬Q→P)} y {¬P→(¬Q→¬P)}.', 'Ahora {A9} con {A} = {¬Q} y {B} = {P}: {(¬Q→P)→((¬Q→¬P)→¬¬Q)}. Dos {MP} te dan {¬¬Q}.', 'Con {A10} sobre {Q} y un {MP}, quitas la doble negación.'],
      sol: [ax('A1', { A: 'P', B: '¬Q' }), ['MP', [3, 1]], ax('A1', { A: '¬P', B: '¬Q' }), ['MP', [5, 2]], ax('A9', { A: '¬Q', B: 'P' }), ['MP', [7, 4]], ['MP', [8, 6]], ax('A10', { A: 'Q' }), ['MP', [10, 9]]] }),
    P('Reducción al absurdo', ['P→⊥'], '¬P', 'cNeg', { sys: 'H',
      intro: 'Si suponer {P} lleva a {⊥}, entonces {¬P}. Con {A9} sobre {⊥} y el axioma del absurdo.',
      hints: ['{A9} con {A} = {P} y {B} = {⊥}: {(P→⊥)→((P→¬⊥)→¬P)}. Un {MP} con la premisa.', 'Falta {P→¬⊥}. Pulsa {A14} para obtener {¬⊥} y {A1} con {A} = {¬⊥} y {B} = {P}.', 'Un {MP} entre ellas da {P→¬⊥}; el último {MP} termina.'],
      sol: [ax('A9', { A: 'P', B: '⊥' }), ['MP', [2, 1]], ['A14'], ax('A1', { A: '¬⊥', B: 'P' }), ['MP', [5, 4]], ['MP', [3, 6]]] }),
    P('La doble negación a mano', ['¬¬P'], 'P', 'cNeg', { sys: 'H',
      intro: 'Con {A10} es inmediato. Es la regla ¬¬E desmontada.',
      hints: ['Pulsa {A10} con {A} = {P}.', 'Un {MP} con la premisa.'],
      sol: [ax('A10', { A: 'P' }), ['MP', [2, 1]]] }),
    T('La caja de herramientas', [
      { say: 'Con lo que acabas de demostrar tienes cuatro reglas más: {¬I}, {¬E}, {⊥E} y {¬¬E}. Ya no hace falta volver a los axiomas cada vez. Y como sabes que cualquier instancia de lo que demostraste vale, puedes usar esas reglas con cualquier fórmula.' },
      { say: 'Mira cómo funciona <b>¬I</b> con subprueba: supones {A}; si llegas a {⊥}, concluyes {¬A}. Es el teorema de la deducción más la reducción al absurdo que acabas de demostrar.',
        fig: fitch([['i', 1, 'A', 'Supuesto', 'h'], ['', 1, '⋮', ''], ['j', 1, '⊥', ''], ['', 0, '¬A', '¬I i–j']]) },
      { say: 'Y <b>¬E</b> y <b>⊥E</b>: de una fórmula y su negación sale {⊥}, y de {⊥} sale lo que quieras.',
        fig: [fitch([['m', 0, 'A', ''], ['n', 0, '¬A', ''], ['', 0, '⊥', '¬E m, n']]), fitch([['m', 0, '⊥', ''], ['', 0, 'A', '⊥E m']])] }
    ]),
    P('Modus tollens', ['P→Q', '¬Q'], '¬P', 'neg', {
      intro: 'Para probar una negación, supón lo contrario y busca el absurdo.',
      hints: ['Supón {P}.', 'Con {MP} obtienes {Q}, que choca con la premisa {¬Q}: aplica {¬E}.', 'Con {⊥} al final de la subprueba, pulsa {¬I}.'],
      sol: [['H', 'P'], ['MP', [1, 3]], ['¬E', [4, 2]], ['¬I']] }),
    P('No contradicción', [], '¬(P∧¬P)', 'neg', {
      intro: 'El principio de no contradicción, como teorema.',
      hints: ['Supón {P∧¬P}.', 'Sepárala con {∧E} en {P} y {¬P}.', 'Aplica {¬E} y cierra con {¬I}.'],
      sol: [['H', 'P∧¬P'], ['∧E', [1], 'P'], ['∧E', [1], '¬P'], ['¬E', [2, 3]], ['¬I']] }),
    P('Silogismo disyuntivo', ['P∨Q', '¬P'], 'Q', 'neg', {
      intro: 'Uno de los dos casos es imposible. Ahí es donde hace falta {⊥E}.',
      hints: ['Caso {P}: choca con {¬P}. Aplica {¬E} y luego {⊥E} para obtener {Q}. Cierra la subprueba.', 'Caso {Q}: supón {Q} y ya está: la subprueba empieza y termina en {Q}.', 'Pulsa {∨E}.'],
      sol: [['H', 'P'], ['¬E', [3, 2]], ['⊥E', [4], null, 'Q'], ['C'], ['H', 'Q'], ['∨E', [1]]] }),
    P('Contraposición', ['¬Q→¬P'], 'P→Q', 'neg', {
      intro: 'Esta dirección de la contraposición necesita {¬¬E}.',
      hints: ['Supón {P}. Dentro, supón {¬Q} para buscar el absurdo.', 'Con {MP} obtienes {¬P}, que choca con {P}.', 'Tras {¬I} tendrás {¬¬Q}: quítale la doble negación con {¬¬E} y cierra con {TD}.'],
      sol: [['H', 'P'], ['H', '¬Q'], ['MP', [1, 3]], ['¬E', [2, 4]], ['¬I'], ['¬¬E', [6]], ['TD']] }),
    P('Tercero excluido', [], 'P∨¬P', 'neg', {
      boss: true,
      intro: 'El teorema más famoso de la lógica clásica. No se puede probar directamente: hay que suponer que es falso.',
      hints: ['Supón {¬(P∨¬P)}. El plan es llegar a {⊥}, obtener la doble negación y quitarla con {¬¬E}.', 'Dentro, supón {P}: con {∨I} tendrías {P∨¬P}, que contradice el supuesto. Así obtienes {¬P} con {¬I}.', 'Con {¬P} vuelve a formar {P∨¬P} con {∨I}: otra contradicción. Cierra con {¬I} y aplica {¬¬E}.'],
      sol: [['H', '¬(P∨¬P)'], ['H', 'P'], ['∨I', [2], 'P∨¬P', '¬P'], ['¬E', [3, 1]], ['¬I'], ['∨I', [5], 'P∨¬P', 'P'], ['¬E', [6, 1]], ['¬I'], ['¬¬E', [8]]] }),
    T('Bicondicional: A11, A12 y A13', [
      { say: '{A↔B} equivale a dos condicionales: {A→B} y {B→A}. Sus tres axiomas lo dicen.',
        fig: table(['Nombre', 'Esquema', 'Idea'], [['{A11}', '{(A↔B)→(A→B)}', 'de izquierda a derecha'], ['{A12}', '{(A↔B)→(B→A)}', 'de derecha a izquierda'], ['{A13}', '{(A→B)→((B→A)→(A↔B))}', 'juntar los dos sentidos']]) },
      { say: 'Con {A11}, {A12} y dos {MP} se obtiene la regla <b>↔E</b>. Con {A13} se arma <b>↔I</b>, que se usa con dos subpruebas: una de {A} a {B} y otra de {B} a {A}.',
        fig: fitch([['i', 1, 'A', 'Supuesto', 'h'], ['j', 1, 'B', ''], ['k', 1, 'B', 'Supuesto', 'h'], ['l', 1, 'A', ''], ['', 0, 'A↔B', '↔I i–j, k–l']]) }
    ]),
    P('Construye ↔E', ['P↔Q', 'Q'], 'P', 'cIff', { sys: 'H',
      intro: 'Con el bicondicional y uno de sus lados, el otro. Esta vez de derecha a izquierda.',
      hints: ['Pulsa {A12} con {A} = {P} y {B} = {Q}: {(P↔Q)→(Q→P)}.', 'Un {MP} con la premisa {P↔Q} y otro con {Q}.'],
      sol: [ax('A12', { A: 'P', B: 'Q' }), ['MP', [3, 1]], ['MP', [4, 2]]] }),
    P('Construye ↔I', ['P→Q', 'Q→P'], 'P↔Q', 'cIff', { sys: 'H',
      intro: 'Dos condicionales hacen un bicondicional, con {A13}.',
      hints: ['Pulsa {A13} con {A} = {P} y {B} = {Q}.', 'Un {MP} con {P→Q} y otro con {Q→P}.'],
      sol: [ax('A13', { A: 'P', B: 'Q' }), ['MP', [3, 1]], ['MP', [4, 2]]] }),
    P('Cadena de equivalencias', ['P↔Q', 'Q↔R'], 'P↔R', 'cl', {
      intro: 'Dos subpruebas: de {P} a {R} y de {R} a {P}.',
      hints: ['Supón {P}. Con {↔E} pasa a {Q} y luego a {R}. Pulsa <b>Cerrar sub.</b>', 'Supón {R} y haz el camino inverso hasta {P}.', 'Pulsa {↔I} y elige {P↔R}.'],
      sol: [['H', 'P'], ['↔E', [1, 3], 'Q'], ['↔E', [2, 4], 'R'], ['C'], ['H', 'R'], ['↔E', [2, 6], 'Q'], ['↔E', [1, 7], 'P'], ['↔I', [], 'P↔R']] }),
    T('Verdad y contraejemplos', [
      { say: 'Hasta ahora has <i>derivado</i> fórmulas. ¿Y las que no se pueden derivar? Para eso está la semántica. Una <b>valuación</b> asigna a cada letra un valor: verdadero (V) o falso (F), y las tablas calculan el resto.',
        fig: table(['{A}', '{B}', '{A∧B}', '{A∨B}', '{A→B}'], [['V', 'V', 'V', 'V', 'V'], ['V', 'F', 'F', 'V', 'F'], ['F', 'V', 'F', 'V', 'V'], ['F', 'F', 'F', 'F', 'V']]) },
      { say: 'Los axiomas que has usado son <b>tautologías</b>: verdaderos en todas las valuaciones. Y el modus ponens conserva la verdad: si {A→B} y {A} son verdaderas, {B} también. Por eso todo lo que se deriva es válido. Es la <b>corrección</b> del cálculo.' },
      { say: 'Un argumento es válido si <i>ninguna</i> valuación hace verdaderas las premisas y falsa la conclusión. Una valuación así es un <b>contraejemplo</b>. Si existe, no hay derivación posible. En los dos retos siguientes encuentra el contraejemplo: cambia los valores hasta que todas las premisas sean verdaderas y la conclusión falsa.' }
    ]),
    M('Afirmar el consecuente', 'CL', ['P→Q', 'Q'], 'P', {
      intro: 'Una falacia clásica. Busca valores que hagan verdaderas las premisas y falsa la conclusión.',
      outro: 'Con {P} falsa y {Q} verdadera, las dos premisas son verdaderas y la conclusión falsa. Por eso «afirmar el consecuente» es una falacia: ninguna derivación la alcanza.' }),
    M('La o inclusiva', 'CL', ['P∨Q', 'P'], '¬Q', {
      intro: 'En lógica, {∨} es inclusiva. Muestra que de {P∨Q} y {P} no se sigue {¬Q}.',
      outro: 'Si las dos son verdaderas, {P∨Q} es verdadera. La disyunción lógica no excluye que se den ambas.' }),
    P('De Morgan', ['¬(P∧Q)'], '¬P∨¬Q', 'neg', {
      boss: true,
      intro: 'El jefe del mundo. La estrategia es la del tercero excluido: supón que la conclusión es falsa.',
      hints: ['Supón {¬(¬P∨¬Q)}. Quieres recuperar {P} y {Q} para contradecir la premisa.', 'Para {P}: supón {¬P}, forma {¬P∨¬Q} con {∨I}, contradicción, {¬I} y {¬¬E}. Haz lo mismo para {Q}.', 'Une {P} y {Q} con {∧I}, aplica {¬E} con la premisa, cierra con {¬I} y termina con {¬¬E}.'],
      sol: [['H', '¬(¬P∨¬Q)'], ['H', '¬P'], ['∨I', [3], '¬P∨¬Q', '¬Q'], ['¬E', [4, 2]], ['¬I'], ['¬¬E', [6]],
        ['H', '¬Q'], ['∨I', [8], '¬P∨¬Q', '¬P'], ['¬E', [9, 2]], ['¬I'], ['¬¬E', [11]],
        ['∧I', [7, 12], 'P∧Q'], ['¬E', [13, 1]], ['¬I'], ['¬¬E', [15]]] }),
    V('El oráculo de la pradera', 'cl', { syms: '¬∧∨→↔⊥', goals: ['valid', 'invalid', 'own'],
      intro: 'El oráculo no hace derivaciones: revisa todas las valuaciones. Si dice «válido», existe una derivación de Hilbert, aunque él no la escriba: es la <b>completitud</b>. Si dice «no válido», te enseña el contraejemplo y te ahorras buscar una derivación que no existe.',
      outro: 'Corrección y completitud juntas: un argumento proposicional tiene derivación exactamente cuando ninguna valuación lo refuta.',
      ex: [[['P→Q', 'Q→R'], 'P→R', 'valid'], [['P∨Q', 'P→R', 'Q→R'], 'R', 'valid'], [['¬(P∧Q)'], '¬P∨¬Q', 'valid'], [['P∨Q', 'P'], '¬Q', 'invalid'], [['P→Q'], 'Q→P', 'invalid'], [['(P∧Q)→R'], '(P→R)∨(Q→R)', 'valid'], [[], '((P→Q)→P)→P', 'valid']] })
  ]
};

/* ============ MUNDO 2 · primer orden ============ */
const w2 = {
  k: 2, name: 'Bosque de los Cuantificadores', logic: 'Lógica de primer orden', badge: '∀',
  intro: 'Entre estos árboles las oraciones se abren: hay individuos, propiedades y dos cuantificadores, con sus propios axiomas.',
  stages: [
    T('Nombres, predicados y cuantificadores', [
      { say: 'La lógica proposicional no ve dentro de las oraciones. La de <b>primer orden</b> sí: distingue individuos y lo que se dice de ellos. Los <b>nombres</b> ({a}, {b}, {c}…) designan individuos; los <b>predicados</b> ({F}, {G}, {R}…) expresan propiedades y relaciones.',
        fig: table(['Fórmula', 'Se lee'], [['{Fa}', 'a es F'], ['{Rab}', 'a está en la relación R con b'], ['{∀xFx}', 'todo es F'], ['{∃xFx}', 'algo es F']]) },
      { say: 'Los <b>cuantificadores</b> usan variables ({x}, {y}, {z}). «Todos los humanos son mortales» se escribe {∀x(Hx→Mx)}. «Algún humano es sabio» se escribe {∃x(Hx∧Sx)}. Fíjate en el patrón: {∀} suele ir con {→}, y {∃} con {∧}.' },
      { say: 'Todo lo que demostraste en la Pradera sigue valiendo, con fórmulas de primer orden. Hilbert añadió <b>cuatro axiomas</b> y <b>una regla</b> para manejar los cuantificadores.' }
    ]),
    T('Los axiomas de los cuantificadores', [
      { say: 'Lo que es verdad de todo, es verdad de cualquier individuo; y si un individuo cumple algo, entonces algo lo cumple. Son los dos primeros axiomas.',
        fig: table(['Nombre', 'Esquema', 'Idea'], [['{Q1}', '{∀xA(x)→A(c)}', 'de todos, a uno cualquiera'], ['{Q2}', '{A(c)→∃xA(x)}', 'de uno, a alguno']]) },
      { say: 'En el juego, con {Q1} escribes el universal ({∀xFx}) y eliges el nombre {c}. Con {Q2} escribes la fórmula con el nombre ({Fa}) y eliges qué apariciones del nombre se cambian por la variable.' },
      { say: 'Los otros dos axiomas ponen condiciones sobre dónde puede estar libre la variable {x}.',
        fig: table(['Nombre', 'Esquema', 'Condición'], [['{Q3}', '{∀x(A→B)→(A→∀xB)}', '{x} no está libre en {A}'], ['{Q4}', '{∀x(A→B)→(∃xA→B)}', '{x} no está libre en {B}']]) },
      { say: 'Y una regla, la <b>generalización</b>: de {A(c)} se concluye {∀xA(x)}, <i>siempre que el nombre {c} no figure en las premisas</i>. Sin esa condición se demostraría cualquier cosa.',
        fig: fitch([['m', 0, 'A(c)', ''], ['', 0, '∀xA(x)', 'Gen m']]) }
    ]),
    P('Sócrates a mano', ['∀x(Hx→Mx)', 'Hs'], 'Ms', 'q0', { sys: 'H',
      intro: 'Todos los humanos son mortales. Sócrates es humano. Ya sabes cómo acaba; ahora, con {Q1} y {MP}.',
      hints: ['Pulsa {Q1}, escribe {∀x(Hx→Mx)} y elige el resultado con el nombre {s}: {∀x(Hx→Mx)→(Hs→Ms)}.', 'Un {MP} con la premisa 1 te da {Hs→Ms}.', 'Otro {MP} con {Hs} termina.'],
      sol: [ax('Q1', { A: '∀x(Hx→Mx)' }, '∀x(Hx→Mx)→(Hs→Ms)'), ['MP', [3, 1]], ['MP', [4, 2]]] }),
    P('Construye ∀E', ['∀xFx'], 'Fa', 'q0', { sys: 'H',
      intro: 'De un universal a un caso. Esta es la regla ∀E, desmontada.',
      hints: ['Pulsa {Q1}, escribe {∀xFx} y elige el resultado con el nombre {a}.', 'Un {MP} con la premisa.'],
      sol: [ax('Q1', { A: '∀xFx' }, '∀xFx→Fa'), ['MP', [2, 1]]] }),
    P('Construye ∃I', ['Fa'], '∃xFx', 'q0', { sys: 'H',
      intro: 'De un ejemplo a un existencial. Esta es la regla ∃I, desmontada.',
      hints: ['Pulsa {Q2} y escribe {Fa}. Elige el resultado {Fa→∃xFx}.', 'Un {MP} con la premisa.'],
      sol: [ax('Q2', { A: 'Fa' }, 'Fa→∃xFx'), ['MP', [2, 1]]] }),
    P('De todos a alguno', ['∀xFx'], '∃xFx', 'fo1', {
      intro: 'En lógica clásica el dominio nunca está vacío: si todo es {F}, algo es {F}. Ahora con las reglas derivadas {∀E} y {∃I}.',
      hints: ['Baja al caso particular con {∀E}: obtendrás {Fa}.', 'Sube con {∃I} desde {Fa}.'],
      sol: [['∀E', [1], 'Fa'], ['∃I', [2], '∃xFx']] }),
    P('Narciso', ['Laa'], '∃xLxa', 'fo1', {
      intro: '{Laa} dice que a se ama a sí mismo. Prueba que alguien ama a a. Tendrás que elegir qué aparición del nombre se sustituye.',
      hints: ['Selecciona la línea 1 y pulsa {∃I}.', 'De la lista, elige {∃xLxa}: solo se sustituye la primera {a}.'],
      sol: [['∃I', [1], '∃xLxa']] }),
    T('Gen: el individuo arbitrario', [
      { say: '¿Cómo se prueba que <i>todo</i> es {F}? No puedes revisar los individuos uno por uno. La idea es probarlo de un individuo <b>arbitrario</b>: uno del que no sabes nada especial.' },
      { say: 'Regla <b>Gen</b>: de {A(c)} concluye {∀xA(x)}, siempre que el nombre {c} no aparezca en ninguna premisa ni en ningún supuesto abierto. Esa condición garantiza que {c} es de verdad arbitrario.',
        fig: fitch([['m', 0, 'A(c)', ''], ['', 0, '∀xA(x)', 'Gen m']]) },
      { say: 'Si la premisa fuera {Fa}, no podrías concluir {∀xFx}: de {a} sabes algo particular. El juego te avisará cuando un nombre no sea arbitrario.' }
    ]),
    P('Barbara', ['∀x(Fx→Gx)', '∀xFx'], '∀xGx', 'fo2', {
      intro: 'Baja a un individuo cualquiera, razona con él y vuelve a subir.',
      hints: ['Aplica {∀E} a las dos premisas con el mismo nombre {a}.', 'Con {MP} obtén {Ga}.', 'Como {a} no aparece en ninguna premisa, puedes aplicar {Gen} a {Ga}.'],
      sol: [['∀E', [1], 'Fa→Ga'], ['∀E', [2], 'Fa'], ['MP', [3, 4]], ['Gen', [5], '∀xGx']] }),
    P('Repartir el todo', ['∀x(Fx∧Gx)'], '∀xFx∧∀xGx', 'fo2', {
      intro: 'El universal se reparte sobre la conjunción.',
      hints: ['{∀E} sobre la premisa y luego {∧E} dos veces: obtienes {Fa} y {Ga}.', 'Generaliza cada una con {Gen}.', 'Une los dos universales con {∧I}.'],
      sol: [['∀E', [1], 'Fa∧Ga'], ['∧E', [2], 'Fa'], ['∧E', [2], 'Ga'], ['Gen', [3], '∀xFx'], ['Gen', [4], '∀xGx'], ['∧I', [5, 6], '∀xFx∧∀xGx']] }),
    P('Un cuantificador que cruza', ['∀x(P→Fx)'], 'P→∀xFx', 'fo2q', {
      intro: 'Si {P} implica {Fx} para todo {x}, entonces {P} implica que todo es {F}. Aquí {x} no está libre en {P}: puede aplicarse {Q3}.',
      hints: ['Pulsa {Q3} y escribe {∀x(P→Fx)}.', 'Un {MP} con la premisa. (Hay otro camino: supón {P}, baja con {∀E}, sube con {Gen} y cierra con {TD}.)'],
      sol: [ax('Q3', { A: '∀x(P→Fx)' }), ['MP', [2, 1]]] }),
    T('Q4 y el existencial', [
      { say: 'Sabes que algo es {F}, pero no sabes qué. Si de «cualquier {F} se sigue {B}» y hay algún {F}, entonces {B}. Eso dice el axioma {Q4}: {∀x(A→B)→(∃xA→B)}, con {x} no libre en {B}.' },
      { say: 'De {Q4} sale la regla <b>∃E</b>: ponerle un nombre provisional al individuo que existe. Abres una subprueba suponiendo {A(c)}, con un nombre <b>nuevo</b>. Si dentro llegas a una fórmula {B} que ya no menciona {c}, puedes sacarla fuera.',
        fig: fitch([['m', 0, '∃xA(x)', ''], ['i', 1, 'A(c)', 'Supuesto', 'h'], ['', 1, '⋮', ''], ['j', 1, 'B', ''], ['', 0, 'B', '∃E m, i–j']]) },
      { say: 'Condiciones: {c} no aparece antes (ni en premisas, ni en supuestos abiertos, ni en el existencial) y tampoco en {B}. Para ver que sale de los axiomas, la próxima derivación la haces a mano: el supuesto se cierra con {TD}, se generaliza con {Gen} y entra {Q4}.' }
    ]),
    P('Construye ∃E', ['∃y(Fy∧Gy)'], '∃xFx', 'cEx', { sys: 'H',
      intro: 'De «algo es F y G» a «algo es F», sin ∃E. Supón la instancia con un nombre nuevo, llega a la conclusión, ciérrala con {TD}, generaliza con {Gen} y usa {Q4}.',
      hints: ['Supón {Fa∧Ga}. Con {∧E} y {∃I} llegas a {∃xFx}. Cierra con {TD}: {(Fa∧Ga)→∃xFx}.', 'El nombre {a} no figura en la premisa: {Gen} te da {∀y((Fy∧Gy)→∃xFx)}.', '{Q4} con esa fórmula da {∃y(Fy∧Gy)→∃xFx}. Un {MP} con la premisa termina.'],
      sol: [['H', 'Fa∧Ga'], ['∧E', [2], 'Fa'], ['∃I', [3], '∃xFx'], ['TD'], ['Gen', [5], '∀y((Fy∧Gy)→∃xFx)'], ax('Q4', { A: '∀y((Fy∧Gy)→∃xFx)' }), ['MP', [7, 6]], ['MP', [8, 1]]] }),
    P('Quedarse con una parte', ['∃x(Fx∧Gx)'], '∃xFx', 'fo', {
      intro: 'Ahora con {∃E}: ponle nombre al individuo que existe y trabaja con él.',
      hints: ['Pulsa <b>Suponer</b> y elige la instancia {Fa∧Ga}.', 'Dentro: {∧E} para obtener {Fa} y luego {∃I}.', 'La última línea, {∃xFx}, ya no menciona {a}: pulsa {∃E}.'],
      sol: [['H', 'Fa∧Ga'], ['∧E', [2], 'Fa'], ['∃I', [3], '∃xFx'], ['∃E', [1]]] }),
    P('Darii', ['∀x(Fx→Gx)', '∃xFx'], '∃xGx', 'fo', {
      intro: 'Todo F es G, y algo es F.',
      hints: ['Supón {Fa}, la instancia del existencial.', 'Aplica {∀E} a la línea 1 con el mismo nombre {a} y luego {MP}.', 'Generaliza con {∃I} y sal de la subprueba con {∃E}.'],
      sol: [['H', 'Fa'], ['∀E', [1], 'Fa→Ga'], ['MP', [4, 3]], ['∃I', [5], '∃xGx'], ['∃E', [2]]] }),
    P('Nadie', ['¬∃xFx'], '∀x¬Fx', 'fo', {
      intro: 'Si no hay ningún F, entonces todos son no-F.',
      hints: ['Supón {Fa} para un individuo cualquiera.', 'Con {∃I} obtienes {∃xFx}, que contradice la premisa. Cierra con {¬I}.', 'Tienes {¬Fa} y {a} no aparece en ninguna premisa: aplica {Gen}.'],
      sol: [['H', 'Fa'], ['∃I', [2], '∃xFx'], ['¬E', [3, 1]], ['¬I'], ['Gen', [5], '∀x¬Fx']] }),
    P('Orden de cuantificadores', ['∃x∀yRxy'], '∀y∃xRxy', 'fo', {
      intro: 'Si alguien se relaciona con todos, entonces con cada uno se relaciona alguien.',
      hints: ['Supón la instancia {∀yRay}.', 'Con {∀E} elige el resultado con un nombre nuevo: {Rab}.', 'Aplica {∃I} para obtener {∃xRxb}, luego {Gen} sobre {b}, y sal con {∃E}.'],
      sol: [['H', '∀yRay'], ['∀E', [2], 'Rab'], ['∃I', [3], '∃xRxb'], ['Gen', [4], '∀y∃xRxy'], ['∃E', [1]]] }),
    Q('¿Y al revés?', [
      { q: 'Acabas de probar que {∃x∀yRxy} implica {∀y∃xRxy}. ¿Vale también la inversa?',
        opts: ['Sí, son equivalentes', 'No: «cada uno tiene una madre» no implica «hay una madre de todos»', 'Solo si el dominio es infinito'], ok: 1,
        why: 'Lee {Rxy} como «x es madre de y». Que cada uno tenga su madre no significa que exista una única madre de todos. Si intentas la derivación, la condición del nombre nuevo te bloquea.' },
      { q: '¿Por qué {Gen} exige que el nombre no aparezca en premisas ni en supuestos abiertos?',
        opts: ['Para que la prueba sea más corta', 'Porque el nombre debe representar a un individuo cualquiera', 'Porque los nombres no pueden repetirse'], ok: 1,
        why: 'Si sabes algo especial de {a}, lo que pruebes de {a} puede depender de eso y no valer para los demás.' }
    ]),
    P('Alguno no', ['¬∀xFx'], '∃x¬Fx', 'fo', {
      boss: true,
      intro: 'El jefe del bosque. Es una prueba clásica: necesitarás {¬¬E} dos veces.',
      hints: ['Supón {¬∃x¬Fx}. El plan: probar {∀xFx} para contradecir la premisa.', 'Dentro, supón {¬Fa}. Con {∃I} contradices el supuesto; {¬I} y {¬¬E} te dan {Fa}.', 'Generaliza a {∀xFx} con {Gen}, contradice la premisa, cierra con {¬I} y termina con {¬¬E}.'],
      sol: [['H', '¬∃x¬Fx'], ['H', '¬Fa'], ['∃I', [3], '∃x¬Fx'], ['¬E', [4, 2]], ['¬I'], ['¬¬E', [6]], ['Gen', [7], '∀xFx'], ['¬E', [8, 1]], ['¬I'], ['¬¬E', [10]]] }),
    V('El vigía del bosque', 'cl', { syms: '¬∧∨→↔⊥∀∃', goals: ['valid', 'invalid', 'own'],
      intro: 'Con cuantificadores ya no hay una tabla finita. El vigía busca contramodelos con pocos individuos y, a la vez, intenta cerrar todas las ramas de un árbol que supone las premisas verdaderas y la conclusión falsa. Con predicados de un solo lugar, como {Fx}, siempre llega a una respuesta.',
      outro: 'Church y Turing probaron en 1936 que ningún método decide siempre la validez en primer orden. Con relaciones como {Rxy}, el vigía a veces tendrá que decir «no lo sé».',
      ex: [[['∀x(Hx→Mx)', 'Hs'], 'Ms', 'valid'], [['∃x∀yRxy'], '∀y∃xRxy', 'valid'], [['∀y∃xRxy'], '∃x∀yRxy', 'invalid'], [['∃xFx', '∃xGx'], '∃x(Fx∧Gx)', 'invalid'], [['∀x(Fx∨Gx)'], '∀xFx∨∀xGx', 'invalid'], [['¬∀xFx'], '∃x¬Fx', 'valid']] })
  ]
};

/* ============ MUNDO 3 · modal proposicional ============ */
const w3 = {
  k: 3, name: 'Archipiélago de los Mundos', logic: 'Lógica modal proposicional', badge: '□',
  intro: 'Cada isla es un mundo posible. Lo necesario vale en todas las que alcanzas; lo posible, en alguna. Y cada sistema es un cálculo de Hilbert con sus propios axiomas.',
  stages: [
    T('Necesario y posible', [
      { say: 'Bienvenido al archipiélago. Aquí las oraciones no son verdaderas o falsas sin más: lo son <b>en un mundo posible</b>. Añadimos dos operadores: {□A}, «es necesario que A», y {◇A}, «es posible que A».' },
      { say: 'Un <b>modelo de Kripke</b> tiene mundos y una relación de <b>accesibilidad</b> entre ellos. {□A} es verdadera en un mundo si {A} lo es en todos los mundos accesibles desde él. {◇A} lo es si {A} es verdadera en alguno.',
        fig: { k: 'kripke', h: 150, w: [{ id: 'w1', x: 10, y: 50, t: '' }, { id: 'w2', x: 190, y: 6, t: 'P' }, { id: 'w3', x: 190, y: 94, t: 'P, Q' }], e: [['w1', 'w2'], ['w1', 'w3']],
          cap: 'En w1 valen {□P} y {◇Q}, pero no {□Q}.' } },
      { say: 'Según las propiedades de la accesibilidad obtenemos distintos sistemas: K, T, S4, S5. Cada uno es el cálculo proposicional de la Pradera más unos pocos axiomas modales. Empezamos por <b>K</b>, el más básico, que no supone nada sobre la relación.' }
    ]),
    T('K y la necesitación', [
      { say: 'El sistema K tiene todo lo del Mundo 1 y, además, un axioma y una regla. El axioma <b>K</b> dice que la caja se reparte sobre el condicional. La regla de <b>necesitación</b> dice que todo teorema es necesario.',
        fig: table(['Nombre', 'Esquema', 'Idea'], [['{K}', '{□(A→B)→(□A→□B)}', 'la necesidad se distribuye'], ['{Nec}', 'de {⊢ A}, {⊢ □A}', 'todo teorema es necesario']]) },
      { say: 'Ojo con la condición de {Nec}: solo se aplica a líneas que se prueban <b>sin premisas ni supuestos abiertos</b>. Si {P} es verdadera, no por eso es necesaria. El juego sigue la pista de qué depende cada línea y te avisa.',
        fig: table(['Sí', 'No'], [['{⊢ P→P}  ⇒  {⊢ □(P→P)}', '{P ⊢ P}  ⇒  {P ⊢ □P}'], ['un axioma o un teorema', 'una premisa, o algo que depende de ella']]) },
      { say: 'La posibilidad no tiene axiomas propios: {◇A} es una abreviatura de {¬□¬A}. La regla <b>Def◇</b> cambia una forma por otra en cualquier lugar de una fórmula.',
        fig: table(['Regla', 'Cambia', 'por'], [['{Def◇}', '{◇A}', '{¬□¬A}'], ['{Def◇}', '{¬□¬A}', '{◇A}']]) }
    ]),
    P('Distribución', ['□(P→Q)', '□P'], '□Q', 'k0', { sys: 'K',
      intro: 'El axioma que da nombre al sistema K, con dos modus ponens.',
      hints: ['Pulsa {K} con {A} = {P} y {B} = {Q}: {□(P→Q)→(□P→□Q)}.', 'Un {MP} con la premisa 1 te da {□P→□Q}.', 'Otro {MP} con {□P} termina. Con esto queda demostrada la regla {RK}.'],
      sol: [ax('K', { A: 'P', B: 'Q' }), ['MP', [3, 1]], ['MP', [4, 2]]] }),
    P('Necesitación', [], '□(P→P)', 'k0', { sys: 'K',
      intro: 'Todo teorema es necesario. Prueba {P→P} y aplica {Nec}.',
      hints: ['Supón {P}.', 'Pulsa {TD}: la subprueba se cierra con {P→P}, que ya no depende de nada.', 'Pulsa {Nec} sobre esa línea.'],
      sol: [['H', 'P'], ['TD'], ['Nec', [2]]] }),
    P('Monotonía', ['□P'], '□(Q∨P)', 'k1', { sys: 'K',
      intro: 'Si {P} es necesaria, también lo es cualquier cosa que se siga de {P}. Es {Nec} más {RK}.',
      hints: ['Supón {P}, deduce {Q∨P} con {∨I} y cierra con {TD}: obtienes el teorema {P→(Q∨P)}.', 'Aplica {Nec} a esa línea.', 'Con {RK} y la premisa, concluye. Esta combinación queda guardada como la regla {Mon}.'],
      sol: [['H', 'P'], ['∨I', [2], 'Q∨P', 'Q'], ['TD'], ['Nec', [4]], ['RK', [5, 1]]] }),
    P('Repartir la caja', ['□(P∧Q)'], '□P∧□Q', 'k', { sys: 'K',
      intro: 'Una caja con una conjunción dentro son dos cajas. Usa un teorema auxiliar y {Mon}.',
      hints: ['Supón {P∧Q}, saca {P} con {∧E} y cierra con {TD}: el teorema {(P∧Q)→P}.', '{Mon} con ese teorema y la premisa te da {□P}. Repite para {Q}.', 'Une {□P} y {□Q} con {∧I}.'],
      sol: [['H', 'P∧Q'], ['∧E', [2], 'P'], ['TD'], ['Mon', [4, 1]], ['H', 'P∧Q'], ['∧E', [6], 'Q'], ['TD'], ['Mon', [8, 1]], ['∧I', [5, 9], '□P∧□Q']] }),
    P('Juntar cajas', ['□P∧□Q'], '□(P∧Q)', 'k', { sys: 'K',
      intro: 'La dirección contraria. Separa primero la premisa. Necesitarás el teorema {P→(Q→(P∧Q))}.',
      hints: ['Con {∧E} obtén {□P} y {□Q}.', 'Supón {P}, supón {Q}, junta con {∧I} y cierra dos veces con {TD}: el teorema {P→(Q→(P∧Q))}.', '{Mon} con {□P} da {□(Q→(P∧Q))}. Después {RK} con {□Q}.'],
      sol: [['∧E', [1], '□P'], ['∧E', [1], '□Q'], ['H', 'P'], ['H', 'Q'], ['∧I', [4, 5], 'P∧Q'], ['TD'], ['TD'], ['Mon', [8, 2]], ['RK', [9, 3]]] }),
    P('Lo imposible lo implica todo', ['¬◇P'], '□(P→Q)', 'k', { sys: 'K',
      intro: 'Una paradoja de la implicación estricta: lo imposible implica estrictamente cualquier cosa.',
      hints: ['{Def◇} desarma la premisa: {¬¬□¬P}. Con {¬¬E}, {□¬P}.', 'Prueba el teorema {¬P→(P→Q)}: supón {¬P}, supón {P}, {¬E}, {⊥E} para {Q}, y cierra dos veces con {TD}.', '{Mon} con ese teorema y {□¬P}.'],
      sol: [['Def◇', [1]], ['¬¬E', [2]], ['H', '¬P'], ['H', 'P'], ['¬E', [5, 4]], ['⊥E', [6], null, 'Q'], ['TD'], ['TD'], ['Mon', [9, 3]]] }),
    P('Posibilidad heredada', ['□(P→Q)', '◇P'], '◇Q', 'k', { sys: 'K', boss: true,
      intro: 'El jefe de K. Para probar {◇Q}, supón {□¬Q} y busca el absurdo.',
      hints: ['Convierte la premisa {◇P} en {¬□¬P} con {Def◇}. Prueba el teorema de la contraposición {(P→Q)→(¬Q→¬P)}.', '{Mon} con ese teorema y la premisa 1 te da {□(¬Q→¬P)}. Supón {□¬Q} y usa {RK}: {□¬P}.', 'Choca con {¬□¬P}. Cierra con {¬I}: {¬□¬Q}. Termina con {Def◇}.'],
      sol: [['Def◇', [2]], ['H', 'P→Q'], ['H', '¬Q'], ['H', 'P'], ['MP', [4, 6]], ['¬E', [7, 5]], ['¬I'], ['TD'], ['TD'], ['Mon', [11, 1]],
        ['H', '□¬Q'], ['RK', [12, 13]], ['¬E', [14, 3]], ['¬I'], ['Def◇', [16]]] }),
    T('Los sistemas T, S4 y S5', [
      { say: 'En K no se puede probar ni siquiera {□P→P}. Para eso hace falta que cada mundo se vea a sí mismo: accesibilidad <b>reflexiva</b>. El sistema <b>T</b> añade el axioma <b>T</b>: {□A→A}.' },
      { say: '<b>S4</b> añade el axioma <b>4</b>: {□A→□□A}. Corresponde a una accesibilidad <b>transitiva</b>.' },
      { say: '<b>S5</b> añade el axioma <b>5</b>: {¬□A→□¬□A}. Corresponde a una relación de <b>equivalencia</b>: todos los mundos se ven entre sí.',
        fig: table(['Sistema', 'Axioma nuevo', 'Accesibilidad', 'Valida'], [['K', 'ninguno', 'cualquiera', '{□(A→B)→(□A→□B)}'], ['T', '{T: □A→A}', 'reflexiva', '{□A→A}'], ['S4', '{4: □A→□□A}', 'reflexiva y transitiva', '{□A→□□A}'], ['S5', '{5: ¬□A→□¬□A}', 'de equivalencia', '{◇A→□◇A}']]) },
      { say: 'Cada sistema incluye los axiomas de los anteriores. En cada reto verás en qué sistema trabajas.' }
    ]),
    P('Lo real es posible', ['P'], '◇P', 't', { sys: 'T',
      intro: 'En T, lo que es verdadero es posible. Usa el axioma {T}.',
      hints: ['Supón {□¬P}.', 'El axioma {T} con {A} = {¬P} y un {MP} te dan {¬P}: contradicción con la premisa.', 'Cierra con {¬I} y aplica {Def◇}.'],
      sol: [['H', '□¬P'], ax('T', { A: '¬P' }), ['MP', [3, 2]], ['¬E', [1, 4]], ['¬I'], ['Def◇', [6]]] }),
    P('Lo necesario es posible', ['□P'], '◇P', 't', { sys: 'T',
      intro: 'Esto no vale en K: un mundo sin mundos accesibles hace verdadera {□P} y falsa {◇P}.',
      hints: ['Supón {□¬P}.', 'Usa el axioma {T} para {P} y para {¬P}: obtienes {P} y {¬P}.', 'Contradicción, {¬I} y {Def◇}.'],
      sol: [['H', '□¬P'], ax('T', { A: 'P' }), ['MP', [3, 1]], ax('T', { A: '¬P' }), ['MP', [5, 2]], ['¬E', [4, 6]], ['¬I'], ['Def◇', [8]]] }),
    P('Necesariamente necesario', ['□P'], '□□P', 's4', { sys: 'S4',
      intro: 'El axioma característico de S4.',
      hints: ['Pulsa el axioma {4} con {A} = {P}.', 'Un {MP} con la premisa.'],
      sol: [ax('4', { A: 'P' }), ['MP', [2, 1]]] }),
    P('Posiblemente posible', ['◇◇P'], '◇P', 's4', { sys: 'S4', boss: true,
      intro: 'En S4 las modalidades repetidas se colapsan. Hay que desarmar los dos {◇} con {Def◇}.',
      hints: ['Supón {□¬P}. El axioma {4} te da {□□¬P}.', 'El teorema {□¬P→¬¬□¬P}: supón {□¬P}, supón {¬□¬P}, {¬E}, {¬I} y cierra con {TD}. Con {Mon} y {□□¬P}, {□¬¬□¬P}.', '{Def◇} dos veces sobre la premisa da {¬□¬¬□¬P}: contradicción. {¬I} y {Def◇}.'],
      sol: [['H', '□¬P'], ax('4', { A: '¬P' }), ['MP', [3, 2]], ['H', '□¬P'], ['H', '¬□¬P'], ['¬E', [5, 6]], ['¬I'], ['TD'], ['Mon', [9, 4]],
        ['Def◇', [1], '¬□¬◇P'], ['Def◇', [11], '¬□¬¬□¬P'], ['¬E', [10, 12]], ['¬I'], ['Def◇', [14]]] }),
    P('Necesariamente posible', ['◇P'], '□◇P', 's5', { sys: 'S5',
      intro: 'El axioma característico de S5: lo posible es necesariamente posible.',
      hints: ['{Def◇} convierte la premisa en {¬□¬P}.', 'El axioma {5} con {A} = {¬P} da {¬□¬P→□¬□¬P}. Un {MP}.', '{Def◇} cambia {¬□¬P} por {◇P} dentro de la caja.'],
      sol: [['Def◇', [1]], ax('5', { A: '¬P' }), ['MP', [3, 2]], ['Def◇', [4]]] }),
    P('El axioma B', ['P'], '□◇P', 's5', { sys: 'S5',
      intro: 'Lo que es verdadero es necesariamente posible. Combina lo que ya sabes de T y de S5.',
      hints: ['Primero prueba {◇P} como en «Lo real es posible»: supón {□¬P}, axioma {T}, contradicción, {¬I} y queda {¬□¬P}.', 'El axioma {5} con {A} = {¬P} da {¬□¬P→□¬□¬P}.', 'Un {MP} y {Def◇} para dejar {□◇P}.'],
      sol: [['H', '□¬P'], ax('T', { A: '¬P' }), ['MP', [3, 2]], ['¬E', [1, 4]], ['¬I'], ax('5', { A: '¬P' }), ['MP', [7, 6]], ['Def◇', [8]]] }),
    Q('Marcos y axiomas', [
      { q: '¿Qué propiedad de la accesibilidad hace válida {□P→P}?', opts: ['Transitividad', 'Reflexividad', 'Simetría'], ok: 1,
        why: 'Si cada mundo se ve a sí mismo, lo que vale en todos los mundos accesibles vale también en el propio.' },
      { q: 'En un mundo desde el que no se accede a ningún otro, ¿qué pasa?', opts: ['Vale {□P} para cualquier P, y no vale ninguna {◇P}', 'No vale ni {□P} ni {◇P}', 'Vale {◇P} para cualquier P'], ok: 0,
        why: '{□P} dice «P vale en todos los mundos accesibles»: si no hay ninguno, se cumple vacíamente. Por eso en K no se prueba {□P→◇P}.' },
      { q: '¿En qué sistema {◇□P} implica {□P}?', opts: ['T', 'S4', 'S5'], ok: 2,
        why: 'En S5 solo cuenta el último operador de una cadena. Es justo lo que vas a probar ahora.' },
      { q: '¿Por qué la necesitación solo se aplica a teoremas y no a premisas?', opts: ['Porque las premisas son falsas', 'Porque que algo sea verdadero no lo hace necesario', 'Porque las premisas no se pueden citar'], ok: 1,
        why: 'Si {P ⊢ □P} valiera, toda verdad sería necesaria y la lógica modal no distinguiría nada.' }
    ]),
    P('Posiblemente necesario', ['◇□P'], '□P', 's5', { sys: 'S5', boss: true,
      intro: 'El jefe del archipiélago. Sobre este principio se apoya el argumento ontológico modal.',
      hints: ['Supón {¬□P} y busca el absurdo.', 'El axioma {5} con {A} = {P} da {¬□P→□¬□P}: un {MP} y tienes {□¬□P}.', '{Def◇} sobre la premisa: {¬□¬□P}. Contradicción, {¬I} y {¬¬E}.'],
      sol: [['H', '¬□P'], ax('5', { A: 'P' }), ['MP', [3, 2]], ['Def◇', [1]], ['¬E', [4, 5]], ['¬I'], ['¬¬E', [7]]] }),
    V('El faro de los mundos', 'modal', { sys: ['K', 'T', 'S4', 'S5'], syms: '¬∧∨→↔⊥□◇', goals: ['valid', 'invalid', 'split'],
      intro: 'El faro decide la validez en K, T, S4 y S5: elige el sistema con los botones de arriba. Si el argumento falla, dibuja un <b>modelo de Kripke</b> con sus mundos, sus flechas de accesibilidad y lo que vale en cada uno.',
      outro: 'Cada axioma corresponde a una propiedad de las flechas: T a la reflexividad, 4 a la transitividad y 5 a la propiedad euclídea.',
      ex: [[['□(P→Q)', '□P'], '□Q', 'valid', 'K'], [['□P'], 'P', 'invalid', 'K'], [['□P'], '□□P', 'invalid', 'T'], [['◇P'], '□◇P', 'invalid', 'S4'], [['P'], '□◇P', 'invalid', 'S4'], [['◇P', '◇Q'], '◇(P∧Q)', 'invalid', 'S5'], [['□(P∨Q)'], '□P∨□Q', 'invalid', 'S5']] })
  ]
};

/* ============ MUNDO 4 · modal de primer orden ============ */
const w4 = {
  k: 4, name: 'Ciudadela De Re', logic: 'Lógica modal de primer orden', badge: '□∀',
  intro: 'Tras estas murallas se cruzan los cuantificadores con la necesidad. Importa mucho quién va primero.',
  stages: [
    T('Cuantificar entre mundos', [
      { say: 'Ahora juntamos todo: los axiomas de los cuantificadores y los modales. Lo nuevo es lo que pasa cuando {□} se cruza con {∀} o {∃}.' },
      { say: 'Compara {□∃xGx} con {∃x□Gx}. La primera es <b>de dicto</b>: en cada mundo hay algún G, quizá uno distinto cada vez. La segunda es <b>de re</b>: hay un individuo concreto que es G en todos los mundos.',
        fig: table(['Fórmula', 'Lectura', 'Ejemplo'], [['{□∃xGx}', 'de dicto', 'Necesariamente, alguien gana la lotería'], ['{∃x□Gx}', 'de re', 'Hay alguien que gana necesariamente']]) },
      { say: 'La lectura de re implica la de dicto, pero no al revés. Lo vas a probar enseguida.' }
    ]),
    T('La fórmula Barcan', [
      { say: 'Ruth Barcan Marcus propuso en 1946 un principio célebre: {∀x□Fx→□∀xFx}. Si cada cosa es necesariamente F, entonces necesariamente todo es F.' },
      { say: '¿Es válido? Depende de los dominios. Si en todos los mundos existen los mismos individuos (<b>dominio constante</b>), sí. Si en otro mundo puede haber individuos nuevos, uno de ellos podría no ser F, y el principio falla.',
        fig: { k: 'kripke', h: 110, w: [{ id: 'w1', x: 10, y: 30, t: 'existe a' }, { id: 'w2', x: 180, y: 30, t: 'existen a, b' }], e: [['w1', 'w2']],
          cap: 'Dominios variables: en w2 hay un individuo b que no existía en w1.' } },
      { say: 'Con los axiomas de la lógica de primer orden más K y la necesitación <i>no se puede demostrar</i> la fórmula Barcan; hay que añadirla como axioma, {BF}. Es justo lo que hacía Marcus. Su conversa, {□∀xFx→∀x□Fx}, en cambio, sí se demuestra con lo que ya tienes. Los nombres designan lo mismo en todos los mundos: es la lógica de dominio constante.' }
    ]),
    P('La conversa de Barcan', ['□∀xFx'], '∀x□Fx', 'qk', { sys: 'K',
      intro: 'La conversa se demuestra sin axiomas nuevos. Fíjate en que el teorema auxiliar se prueba antes de usar {Mon}.',
      hints: ['Supón {∀xFx}, baja con {∀E} a {Fa} y cierra con {TD}: el teorema {∀xFx→Fa}.', '{Mon} con ese teorema y la premisa te da {□Fa}.', 'El nombre {a} no está en la premisa: aplica {Gen}.'],
      sol: [['H', '∀xFx'], ['∀E', [2], 'Fa'], ['TD'], ['Mon', [4, 1]], ['Gen', [5], '∀x□Fx']] }),
    P('Barcan en acción', ['∀x□(Fx∧Gx)'], '□∀xGx', 'qk', { sys: 'K',
      intro: 'Aquí sí hace falta el axioma {BF}: hay que pasar de «cada uno es necesariamente G» a «necesariamente todos son G».',
      hints: ['Baja con {∀E} a {□(Fa∧Ga)}. Supón {Fa∧Ga}, saca {Ga} y cierra con {TD}.', '{Mon} te da {□Ga}; generaliza con {Gen} a {∀x□Gx}.', 'El axioma {BF} con esa fórmula, y un {MP}.'],
      sol: [['∀E', [1], '□(Fa∧Ga)'], ['H', 'Fa∧Ga'], ['∧E', [3], 'Ga'], ['TD'], ['Mon', [5, 2]], ['Gen', [6], '∀x□Gx'], ax('BF', { A: '∀x□Gx' }), ['MP', [8, 7]]] }),
    P('De re a de dicto', ['∃x□Fx'], '□∃xFx', 'qk', { sys: 'K',
      intro: 'Si hay algo que es necesariamente F, entonces necesariamente hay algo que es F.',
      hints: ['Supón la instancia {□Fa}.', 'Dentro, supón {Fa}, aplica {∃I} y cierra con {TD}: el teorema {Fa→∃xFx}.', '{Mon} con {□Fa} da {□∃xFx}. Sal con {∃E}.'],
      sol: [['H', '□Fa'], ['H', 'Fa'], ['∃I', [3], '∃xFx'], ['TD'], ['Mon', [5, 2]], ['∃E', [1]]] }),
    P('Silogismo necesario', ['□∀x(Fx→Gx)', '□Fa'], '□Ga', 'qk', { sys: 'K',
      intro: 'Un silogismo entero, pero dentro de una caja.',
      hints: ['Supón {∀x(Fx→Gx)}, baja con {∀E} a {Fa→Ga} y cierra con {TD}.', '{Mon} con la premisa 1 te da {□(Fa→Ga)}.', 'Con {RK} y la premisa 2, {□Ga}.'],
      sol: [['H', '∀x(Fx→Gx)'], ['∀E', [3], 'Fa→Ga'], ['TD'], ['Mon', [5, 1]], ['RK', [6, 2]]] }),
    P('Esencias realizadas', ['∀x□Fx'], '∃xFx', 'qt', { sys: 'T',
      intro: 'En T lo necesario es verdadero, y el dominio no está vacío.',
      hints: ['{∀E} te da {□Fa}.', 'El axioma {T} con {A} = {Fa} y un {MP} te dan {Fa}.', 'Termina con {∃I}.'],
      sol: [['∀E', [1], '□Fa'], ax('T', { A: 'Fa' }), ['MP', [3, 2]], ['∃I', [4], '∃xFx']] }),
    Q('De dicto y de re', [
      { q: '¿Vale la inversa del reto «De re a de dicto», es decir, de {□∃xFx} a {∃x□Fx}?',
        opts: ['Sí', 'No: que siempre haya un ganador no significa que alguien gane siempre', 'Solo en S5'], ok: 1,
        why: 'En cada mundo puede ganar un individuo distinto. Si intentas la derivación, {∃E} no te deja sacar el nombre de la caja.' },
      { q: '¿Qué supuesto hace válida la fórmula Barcan?', opts: ['Que todos los mundos tengan los mismos individuos', 'Que la accesibilidad sea reflexiva', 'Que no haya nombres'], ok: 0,
        why: 'Con dominio constante, lo que vale de cada individuo de aquí vale de cada individuo de allí, porque son los mismos.' },
      { q: '¿Por qué hay que añadir {BF} como axioma, mientras que su conversa se demuestra?', opts: ['Porque {BF} es falsa', 'Porque con K y la necesitación solo se puede pasar de la caja al cuantificador, no al revés', 'Porque la conversa es trivial'], ok: 1,
        why: 'De {□∀xFx} se baja a cada caso, y eso es lo que permiten {K} y {Mon}. Subir de «cada uno es necesariamente F» a una caja única exige decir que los individuos son los mismos en todos los mundos.' }
    ]),
    P('Posibilidad de re', ['∃x◇Fx'], '◇∃xFx', 'qk', { sys: 'K', boss: true,
      intro: 'El jefe de la ciudadela: quince líneas y varios teoremas auxiliares. Respira hondo.',
      hints: ['Supón la instancia {◇Fa} y ábrela con {Def◇}: {¬□¬Fa}. Dentro, prueba el teorema {¬∃xFx→¬Fa}.', 'Supón {□¬∃xFx}. {Mon} con el teorema te da {□¬Fa}, que choca con {¬□¬Fa}.', 'Cierra con {¬I}, aplica {Def◇} y sal con {∃E}.'],
      sol: [['H', '◇Fa'], ['Def◇', [2]], ['H', '¬∃xFx'], ['H', 'Fa'], ['∃I', [5], '∃xFx'], ['¬E', [6, 4]], ['¬I'], ['TD'],
        ['H', '□¬∃xFx'], ['Mon', [9, 10]], ['¬E', [11, 3]], ['¬I'], ['Def◇', [13]], ['∃E', [1]]] }),
    V('El archivo de la ciudadela', 'modal', { sys: ['K', 'T', 'S4', 'S5'], syms: '¬∧∨→↔⊥∀∃□◇', goals: ['valid', 'invalid', 'split'],
      intro: 'El archivo trabaja con mundos e individuos a la vez, con el mismo dominio en todos los mundos: por eso valen la fórmula Barcan y su conversa. Úsalo para separar lo <i>de dicto</i> de lo <i>de re</i>.',
      outro: 'La lógica modal de primer orden tampoco es decidible: el archivo cierra árboles con mundos e individuos, o busca contramodelos con pocos de cada cosa.',
      ex: [[['∀x□Fx'], '□∀xFx', 'valid', 'K'], [['□∃xFx'], '∃x□Fx', 'invalid', 'K'], [['∃x□Fx'], '□∃xFx', 'valid', 'K'], [['∀x□Fx'], '∃xFx', 'invalid', 'K'], [['◇∃xFx'], '∃x◇Fx', 'valid', 'K'], [['∀x◇Fx'], '◇∀xFx', 'invalid', 'S5']] })
  ]
};

/* ============ MUNDO 5 · intuicionista ============ */
const w5 = {
  k: 5, name: 'Taller del Constructor', logic: 'Lógica intuicionista', badge: '¬¬',
  intro: 'En este taller solo cuenta lo que se construye. Un axioma se queda en la puerta.',
  stages: [
    T('La verdad como construcción', [
      { say: 'Este taller es de L. E. J. Brouwer. Para el <b>intuicionismo</b>, afirmar una proposición matemática es tener una construcción que la pruebe. La verdad no está ahí esperando: se construye.' },
      { say: 'Eso cambia el significado de las conectivas. Es la interpretación BHK (Brouwer, Heyting, Kolmogórov).',
        fig: table(['Una prueba de…', 'consiste en…'], [['{A∧B}', 'una prueba de A y una prueba de B'], ['{A∨B}', 'una prueba de A o una de B, sabiendo cuál'], ['{A→B}', 'un método que convierte pruebas de A en pruebas de B'], ['{¬A}', 'un método que convierte cualquier prueba de A en un absurdo']]) },
      { say: 'Con esa lectura, {P∨¬P} deja de ser obvia: exigiría tener una prueba de {P} o una refutación de {P}, y hay problemas abiertos para los que no tenemos ninguna de las dos.' }
    ]),
    T('Un axioma menos', [
      { say: 'En el cálculo de Hilbert la diferencia es mínima: la lógica intuicionista es la clásica <b>sin el axioma A10</b>, {¬¬A→A}. En su lugar entra una versión más débil, <b>A10i</b>, el principio de explosión: {¬A→(A→B)}.',
        fig: table(['Axioma', 'Esquema', 'Está en'], [['{A10}', '{¬¬A→A}', 'clásica'], ['{A10i}', '{¬A→(A→B)}', 'intuicionista (y también en la clásica, donde se demuestra)']]) },
      { say: 'De {¬¬A} ya no puedes pasar a {A}. Saber que {A} no puede refutarse no es lo mismo que haberla construido. Las demás reglas derivadas se conservan, incluida {⊥E}, que ahora sale de {A10i} sin esfuerzo.',
        fig: table(['Se puede probar', 'No se puede probar'], [['{P→¬¬P}', '{¬¬P→P}'], ['{¬¬¬P→¬P}', '{P∨¬P}'], ['{(P→Q)→(¬Q→¬P)}', '{(¬Q→¬P)→(P→Q)}'], ['{¬(P∨Q)→(¬P∧¬Q)}', '{¬(P∧Q)→(¬P∨¬Q)}']]) },
      { say: 'Mira la barra de reglas en los próximos retos: {¬¬E} ha desaparecido. Vamos a ver cuánto se puede hacer sin ella.' }
    ]),
    P('Explosión en un paso', ['P', '¬P'], 'Q', 'i0', { sys: 'H',
      intro: 'En la Pradera la explosión costó once líneas. Aquí es un axioma: {A10i}.',
      hints: ['Pulsa {A10i} con {A} = {P} y {B} = {Q}: {¬P→(P→Q)}.', 'Un {MP} con {¬P} y otro con {P}.'],
      sol: [ax('A10i', { A: 'P', B: 'Q' }), ['MP', [3, 2]], ['MP', [4, 1]]] }),
    P('La mitad buena', ['P'], '¬¬P', 'int', {
      intro: 'La doble negación sí se puede <i>introducir</i>.',
      hints: ['Supón {¬P}.', 'Choca con la premisa: {¬E}.', 'Pulsa {¬I}.'],
      sol: [['H', '¬P'], ['¬E', [1, 2]], ['¬I']] }),
    P('Triple negación', ['¬¬¬P'], '¬P', 'int', {
      intro: 'Tres negaciones se reducen a una. Dos no se reducen a ninguna.',
      hints: ['Supón {P}. Quieres contradecir {¬¬¬P}, así que necesitas {¬¬P}.', 'Dentro, supón {¬P}: choca con {P}. {¬I} te da {¬¬P}.', '{¬¬P} y la premisa se contradicen: {¬E} y {¬I}.'],
      sol: [['H', 'P'], ['H', '¬P'], ['¬E', [2, 3]], ['¬I'], ['¬E', [5, 1]], ['¬I']] }),
    P('Contraposición constructiva', ['P→Q'], '¬Q→¬P', 'int', {
      intro: 'Esta dirección de la contraposición no necesita {¬¬E}.',
      hints: ['Supón {¬Q} y, dentro, supón {P}.', '{MP} te da {Q}, que choca con {¬Q}.', '{¬I} y después {TD}.'],
      sol: [['H', '¬Q'], ['H', 'P'], ['MP', [1, 3]], ['¬E', [4, 2]], ['¬I'], ['TD']] }),
    P('De Morgan constructivo', ['¬(P∨Q)'], '¬P∧¬Q', 'int', {
      intro: 'Esta ley de De Morgan vale también aquí. La que venciste en el Mundo 1 no.',
      hints: ['Supón {P}; con {∨I} formas {P∨Q}, que contradice la premisa. {¬I} da {¬P}.', 'Repite con {Q} para obtener {¬Q}.', 'Une con {∧I}.'],
      sol: [['H', 'P'], ['∨I', [2], 'P∨Q', 'Q'], ['¬E', [3, 1]], ['¬I'], ['H', 'Q'], ['∨I', [6], 'P∨Q', 'P'], ['¬E', [7, 1]], ['¬I'], ['∧I', [5, 9], '¬P∧¬Q']] }),
    P('Del «o» al «si»', ['¬P∨Q'], 'P→Q', 'int', {
      intro: 'Vale en esta dirección. La inversa, de {P→Q} a {¬P∨Q}, no es constructiva.',
      hints: ['Supón {P} y razona por casos sobre la premisa.', 'Caso {¬P}: contradicción y {⊥E} para obtener {Q}. Cierra la subprueba.', 'Caso {Q}: basta suponerla. {∨E} y luego {TD}.'],
      sol: [['H', 'P'], ['H', '¬P'], ['¬E', [2, 3]], ['⊥E', [4], null, 'Q'], ['C'], ['H', 'Q'], ['∨E', [1]], ['TD']] }),
    P('Un testigo en contra', ['∃x¬Fx'], '¬∀xFx', 'intfo', {
      intro: 'Un contraejemplo refuta un universal. La inversa («Alguno no», del Mundo 2) no es constructiva: no te da el testigo.',
      hints: ['Supón {∀xFx}. Dentro, supón la instancia {¬Fa}.', '{∀E} te da {Fa}: contradicción.', 'La última línea es {⊥}, que no menciona {a}: pulsa {∃E} y luego {¬I}.'],
      sol: [['H', '∀xFx'], ['H', '¬Fa'], ['∀E', [2], 'Fa'], ['¬E', [4, 3]], ['∃E', [1]], ['¬I']] }),
    T('Estados de conocimiento', [
      { say: 'Kripke dio también una semántica para el intuicionismo. Los puntos son <b>estados de conocimiento</b> ordenados en el tiempo. Lo que ya está probado sigue probado después: el conocimiento solo crece.' },
      { say: '{¬A} vale en un estado si {A} no llega a valer en ningún estado posterior. {A→B} vale si en todo estado posterior donde valga {A} vale también {B}.',
        fig: { k: 'kripke', h: 110, w: [{ id: 'w0', x: 10, y: 30, t: 'nada probado' }, { id: 'w1', x: 200, y: 30, t: 'P' }], e: [['w0', 'w1']],
          cap: 'En w0 no vale {P}: aún no está probada. Tampoco vale {¬P}: en w1 se prueba. Así que en w0 no vale {P∨¬P}.' } },
      { say: 'Ese diagrama es un contramodelo del tercero excluido. Y sin embargo {¬¬(P∨¬P)} sí se puede probar: el tercero excluido no es demostrable, pero tampoco refutable.' }
    ]),
    Q('¿Constructivo o no?', [
      { q: '¿Se puede probar {¬¬P→P} en lógica intuicionista?', opts: ['Sí', 'No'], ok: 1,
        why: 'En el modelo de dos estados, en w0 vale {¬¬P} (no hay estado posterior donde valga {¬P}) pero no vale {P}.' },
      { q: '¿Y {¬(P∧Q)→(¬P∨¬Q)}?', opts: ['Sí', 'No'], ok: 1,
        why: 'Saber que {P} y {Q} no pueden darse juntas no te dice cuál de las dos falla, y una disyunción exige saber cuál.' },
      { q: '¿Y {(¬P∨¬Q)→¬(P∧Q)}?', opts: ['Sí', 'No'], ok: 0,
        why: 'Si tienes refutada una de las dos, cualquier prueba de {P∧Q} lleva al absurdo. Es una prueba por casos corriente.' },
      { q: 'Si en lógica intuicionista se prueba {A∨B} sin premisas, ¿qué más se sabe?', opts: ['Nada más', 'Que se puede probar {A} o se puede probar {B}', 'Que {A} y {B} son equivalentes'], ok: 1,
        why: 'Es la <b>propiedad de la disyunción</b>. La lógica clásica no la tiene: prueba {P∨¬P} sin probar ninguna de las dos.' }
    ]),
    P('Doble negación repartida', ['¬¬(P∧Q)'], '¬¬P', 'int', {
      intro: 'La doble negación atraviesa la conjunción.',
      hints: ['Supón {¬P}. Quieres contradecir la premisa: necesitas {¬(P∧Q)}.', 'Dentro, supón {P∧Q}; {∧E} da {P}, que choca con {¬P}. {¬I}.', '{¬(P∧Q)} contradice la premisa: {¬E} y {¬I}.'],
      sol: [['H', '¬P'], ['H', 'P∧Q'], ['∧E', [3], 'P'], ['¬E', [4, 2]], ['¬I'], ['¬E', [6, 1]], ['¬I']] }),
    P('Tercero no refutable', [], '¬¬(P∨¬P)', 'int', {
      boss: true,
      intro: 'Teorema de Glivenko: si una fórmula proposicional se prueba clásicamente, su doble negación se prueba intuicionistamente. Compruébalo con el tercero excluido.',
      hints: ['Es la prueba del Mundo 1 sin el último paso. Supón {¬(P∨¬P)}.', 'Dentro, supón {P}: {∨I} y contradicción. {¬I} da {¬P}.', 'Con {¬P} forma otra vez {P∨¬P}: contradicción y {¬I}.'],
      sol: [['H', '¬(P∨¬P)'], ['H', 'P'], ['∨I', [2], 'P∨¬P', '¬P'], ['¬E', [3, 1]], ['¬I'], ['∨I', [5], 'P∨¬P', 'P'], ['¬E', [6, 1]], ['¬I']] }),
    P('Glivenko otra vez', [], '¬¬(¬¬P→P)', 'int', {
      boss: true,
      intro: 'El último jefe del taller: la eliminación de la doble negación tampoco es refutable.',
      hints: ['Supón {¬(¬¬P→P)}. Primero prueba {¬P}: supón {P}, y dentro supón {¬¬P} y reitera {P}; {TD} da {¬¬P→P}, contradicción.', 'Ahora, con {¬P}: supón {¬¬P}. Se contradicen; {⊥E} te da {P}.', '{TD} da otra vez {¬¬P→P}: contradicción y {¬I}.'],
      sol: [['H', '¬(¬¬P→P)'], ['H', 'P'], ['H', '¬¬P'], ['R', [2]], ['TD'], ['¬E', [5, 1]], ['¬I'],
        ['H', '¬¬P'], ['¬E', [7, 8]], ['⊥E', [9], null, 'P'], ['TD'], ['¬E', [11, 1]], ['¬I']] }),
    V('El banco de pruebas', 'int', { cmp: 'cl', syms: '¬∧∨→↔⊥', goals: ['valid', 'gap', 'own'],
      intro: 'El banco compara dos lógicas a la vez: la intuicionista y la clásica. Si un argumento falla constructivamente, dibuja los estados de conocimiento que lo refutan: cada flecha lleva a un estado que sabe más.',
      outro: 'Todo argumento intuicionista es clásico, pero no al revés. Lo que se pierde es justo lo que necesita {¬¬E}.',
      ex: [[['P'], '¬¬P', 'valid'], [['¬¬P'], 'P', 'invalid'], [[], 'P∨¬P', 'invalid'], [[], '¬¬(P∨¬P)', 'valid'], [['¬(P∧Q)'], '¬P∨¬Q', 'invalid'], [['P→Q'], '¬P∨Q', 'invalid'], [[], '((P→Q)→P)→P', 'invalid'], [['¬¬¬P'], '¬P', 'valid']] })
  ]
};

/* ============ MUNDO 6 · paraconsistente ============ */
const w6 = {
  k: 6, name: 'Caverna de las Contradicciones', logic: 'Lógica paraconsistente (LP)', badge: '⊥',
  intro: 'Aquí abajo una contradicción no hace estallar nada. Entra con cuidado y sin {⊥E}.',
  stages: [
    T('La explosión', [
      { say: 'Última parada. En lógica clásica e intuicionista vale el principio de <b>explosión</b>: de una contradicción se sigue cualquier cosa, {A, ¬A ⊢ B}. Lo usaste con el nombre de {⊥E}.' },
      { say: 'Eso significa que una teoría con una sola contradicción lo prueba todo y deja de servir. Pero razonamos a diario con información inconsistente: bases de datos con errores, teorías científicas en conflicto, leyes que chocan, paradojas.' },
      { say: 'Una lógica es <b>paraconsistente</b> si rechaza la explosión. Algunos filósofos, como Graham Priest, van más lejos y sostienen que hay contradicciones verdaderas (<b>dialeteísmo</b>). La oración del mentiroso, «esta oración es falsa», sería una.' }
    ]),
    T('LP: tres valores', [
      { say: 'La <b>Lógica de la Paradoja</b> (LP) de Priest añade un tercer valor. Una oración puede ser verdadera (V), falsa (F) o <b>ambas cosas</b> (A).' },
      { say: 'Las conectivas se calculan ordenando los valores: F, A, V. La conjunción toma el menor, la disyunción el mayor, y la negación intercambia V y F y deja A como está.',
        fig: [table(['{A}', '{¬A}'], [['V', 'F'], ['A', 'A'], ['F', 'V']]), table(['{∧}', 'V', 'A', 'F'], [['<b>V</b>', 'V', 'A', 'F'], ['<b>A</b>', 'A', 'A', 'F'], ['<b>F</b>', 'F', 'F', 'F']])] },
      { say: 'Un argumento es válido en LP si, siempre que las premisas son <b>al menos verdaderas</b> (V o A), la conclusión también lo es. V y A son los valores <b>designados</b>.' },
      { say: 'Ahora te toca desactivar la explosión. Busca una valuación donde las premisas sean designadas y la conclusión no.' }
    ]),
    M('Desactivar la bomba', 'LP', ['P', '¬P'], 'Q', {
      intro: 'En lógica clásica esto no tiene contraejemplo. En LP sí: usa el tercer valor.',
      outro: 'Si {P} es verdadera y falsa a la vez, {P} y {¬P} son designadas, y {Q} puede ser simplemente falsa. La explosión no es válida en LP.' }),
    M('Adiós al silogismo disyuntivo', 'LP', ['P∨Q', '¬P'], 'Q', {
      intro: 'El silogismo disyuntivo es el motor oculto de la explosión. Muestra que tampoco vale.',
      outro: 'Falla cuando {P} es verdadera y falsa a la vez. Y como el condicional material {P→Q} es {¬P∨Q}, con él falla también el modus ponens.' }),
    T('Hilbert sin modus ponens', [
      { say: 'LP también se puede presentar a la manera de Hilbert, pero con un giro: el modus ponens del condicional material <b>no es válido</b> (acabas de verlo). Sin {MP} un condicional no sirve para avanzar: aquí no hay axiomas del condicional, ni la regla {TD}, ni {⊥}, ni {¬I}. El cálculo trabaja con un axioma y con reglas que no pasan por el condicional.' },
      { say: 'El único axioma es el tercero excluido, {A∨¬A}. Las reglas de {∧} y de {∨} son las de siempre; {∨E} se usa con una subprueba por caso, y aquí es una regla primitiva, no derivada. La negación se maneja con tres reglas.',
        fig: table(['Regla', 'Qué permite'], [['{DN}', 'pasar de {A} a {¬¬A}, y al revés'], ['{DeM}', 'pasar de {¬(A∧B)} a {¬A∨¬B}, y al revés'], ['{DeM}', 'pasar de {¬(A∨B)} a {¬A∧¬B}, y al revés'], ['{LEM}', 'escribir {A∨¬A} en cualquier momento']]) },
      { say: 'Un dato curioso: LP tiene exactamente los mismos <b>teoremas</b> que la lógica clásica. Hasta {¬(P∧¬P)} es un teorema. Lo que cambia son las <b>inferencias</b> válidas: hay menos.' },
      { say: 'En LP una contradicción puede ser verdadera, y la ley de no contradicción también. Si {P} vale A, tanto {P∧¬P} como {¬(P∧¬P)} valen A.' }
    ]),
    P('De Morgan a secas', ['¬(P∨Q)'], '¬P', 'lp', { sys: 'LP',
      intro: 'Sin reducción al absurdo. La negación se mueve con {DeM}.',
      hints: ['Selecciona la premisa y pulsa {DeM}.', 'Quédate con {¬P} usando {∧E}.'],
      sol: [['DeM', [1]], ['∧E', [2], '¬P']] }),
    P('No contradicción, pese a todo', [], '¬(P∧¬P)', 'lp', { sys: 'LP',
      intro: 'LP admite contradicciones verdaderas y aun así prueba la ley de no contradicción.',
      hints: ['Pulsa {LEM} y elige la fórmula {¬P}: obtienes {¬P∨¬¬P}.', 'Aplícale {DeM}.'],
      sol: [ax('LEM', { A: '¬P' }), ['DeM', [1]]] }),
    P('De Morgan y vuelta', ['¬(P∧Q)'], '¬Q∨¬P', 'lp', { sys: 'LP',
      intro: 'La prueba por casos sigue funcionando como siempre.',
      hints: ['{DeM} sobre la premisa da {¬P∨¬Q}.', 'Caso {¬P}: {∨I} hasta {¬Q∨¬P} y <b>Cerrar sub.</b>', 'Caso {¬Q}: {∨I} y después {∨E}.'],
      sol: [['DeM', [1]], ['H', '¬P'], ['∨I', [3], '¬Q∨¬P', '¬Q'], ['C'], ['H', '¬Q'], ['∨I', [5], '¬Q∨¬P', '¬P'], ['∨E', [2]]] }),
    P('Silogismo disyuntivo con salvedad', ['P', '¬P∨Q'], 'Q∨(P∧¬P)', 'lp', { sys: 'LP',
      intro: 'El silogismo disyuntivo no vale en LP, pero sí una versión prudente: o bien {Q}, o bien hay una contradicción.',
      hints: ['Razona por casos sobre {¬P∨Q}.', 'Caso {¬P}: únela con {P} por {∧I} y pasa a la conclusión con {∨I}. Cierra la subprueba.', 'Caso {Q}: {∨I} directa, y {∨E}.'],
      sol: [['H', '¬P'], ['∧I', [1, 3], 'P∧¬P'], ['∨I', [4], 'Q∨(P∧¬P)', 'Q'], ['C'], ['H', 'Q'], ['∨I', [6], 'Q∨(P∧¬P)', 'P∧¬P'], ['∨E', [2]]] }),
    P('Modus ponens con salvedad', ['¬(P∧¬Q)', 'P'], 'Q∨(P∧¬P)', 'lp', { sys: 'LP', boss: true,
      intro: 'El jefe final. {¬(P∧¬Q)} es otra forma de escribir «si P entonces Q». En LP solo puedes separar el consecuente con una salvedad.',
      hints: ['{DeM} sobre la primera premisa: {¬P∨¬¬Q}.', 'Caso {¬P}: forma {P∧¬P} y aplica {∨I}. Cierra la subprueba.', 'Caso {¬¬Q}: {DN} te da {Q}; luego {∨I} y {∨E}.'],
      sol: [['DeM', [1]], ['H', '¬P'], ['∧I', [2, 4], 'P∧¬P'], ['∨I', [5], 'Q∨(P∧¬P)', 'Q'], ['C'],
        ['H', '¬¬Q'], ['DN', [7], 'Q'], ['∨I', [8], 'Q∨(P∧¬P)', 'P∧¬P'], ['∨E', [3]]] }),
    T('El mapa de las lógicas', [
      { say: 'Has recorrido seis lógicas, todas con su cálculo de Hilbert. Mira qué acepta cada una.',
        fig: table(['Principio', 'Clásica', 'Intuicionista', 'LP'], [['{P∨¬P}', 'sí', 'no', 'sí'], ['{¬¬P ⊢ P}', 'sí', 'no', 'sí'], ['{P, ¬P ⊢ Q}', 'sí', 'sí', 'no'], ['{P∨Q, ¬P ⊢ Q}', 'sí', 'sí', 'no']]) },
      { say: 'La lógica clásica lo acepta todo. La intuicionista renuncia al tercero excluido a cambio de pruebas constructivas. La paraconsistente renuncia a la explosión para convivir con contradicciones. Las modales no quitan nada: añaden operadores para hablar de necesidad y posibilidad.' },
      { say: 'Cada una responde a una idea distinta de qué es la verdad y qué significa que algo se siga de algo. Queda un examen final. Después, la caverna es tuya.' }
    ]),
    Q('Examen final', [
      { q: '¿Qué regla hay que quitarle a la lógica clásica para obtener la intuicionista?', opts: ['{⊥E}', '{¬¬E}', '{TD}'], ok: 1,
        why: 'Sin {¬¬E} no se pueden probar ni {P∨¬P} ni {¬¬P→P}.' },
      { q: '¿A qué líneas puede aplicarse la regla de necesitación?', opts: ['A cualquier línea', 'Solo a las que no dependen de premisas ni supuestos', 'Solo a las premisas'], ok: 1,
        why: 'Un teorema es verdadero en todos los mundos; una premisa solo lo es en el mundo en que se la supone.' },
      { q: '¿Qué tienen en común la lógica clásica y LP?', opts: ['Los mismos teoremas', 'Las mismas inferencias válidas', 'Los mismos valores de verdad'], ok: 0,
        why: 'LP prueba las mismas fórmulas sin premisas, pero valida menos inferencias: fallan la explosión y el silogismo disyuntivo.' },
      { q: '¿Cuál de estas lógicas rechaza {P, ¬P ⊢ Q}?', opts: ['Intuicionista', 'S5', 'LP'], ok: 2,
        why: 'Solo las lógicas paraconsistentes rechazan la explosión. ¡Q.E.D.!' }
    ]),
    V('El detector de explosiones', 'lp', { cmp: 'cl', syms: '¬∧∨→↔', goals: ['valid', 'gap', 'own'],
      intro: 'El detector analiza cada argumento en LP, con los valores V, A y F, y también en la lógica clásica. Busca argumentos clásicamente válidos que fallen en LP: su contraejemplo siempre usa el valor A.',
      outro: 'LP no pierde teoremas, pierde inferencias: las que, como la explosión, pasan de una contradicción a cualquier cosa.',
      ex: [[['P', '¬P'], 'Q', 'invalid'], [['P∨Q', '¬P'], 'Q', 'invalid'], [['P', 'P→Q'], 'Q', 'invalid'], [[], 'P∨¬P', 'valid'], [[], '¬(P∧¬P)', 'valid'], [['¬(P∧Q)'], '¬P∨¬Q', 'valid'], [['P'], 'Q∨¬Q', 'valid']] })
  ]
};

/* ============ MUNDO 7 · intuicionista de primer orden ============ */
const w7 = {
  k: 7, name: 'Jardín de los Testigos', logic: 'Lógica intuicionista de primer orden', badge: '∃',
  intro: 'Aquí afirmar que algo existe obliga a mostrarlo. Cada existencial pide su testigo.',
  stages: [
    T('Cuantificar construyendo', [
      { say: 'Volvemos al taller de Brouwer, ahora con cuantificadores. La lectura constructiva se extiende así: probar {∃xA(x)} es exhibir un individuo concreto, el <b>testigo</b>, junto con una prueba de que cumple {A}.', mood: 'neutral' },
      { say: 'Y probar {∀xA(x)} es dar un método que, para cada individuo, produce una prueba de que cumple {A}.',
        fig: table(['Una prueba de…', 'consiste en…'], [['{∃xA(x)}', 'un testigo c y una prueba de {A(c)}'], ['{∀xA(x)}', 'un método que da una prueba de {A(c)} para cada c'], ['{¬∃xA(x)}', 'un método que lleva al absurdo cualquier testigo']]) },
      { say: 'Los axiomas y las reglas de los cuantificadores son los del Mundo 2: {Q1} a {Q4}, {Gen}, {∀E}, {∃I} y {∃E}. Lo único que falta, como en el Mundo 5, es {A10}, o sea, {¬¬E}. Por eso «no todos son F» ya no basta para concluir «hay uno que no es F»: nadie te ha dado el testigo.' },
      { say: 'A cambio se gana la <b>propiedad de la existencia</b>: si la lógica intuicionista prueba {∃xA(x)} sin premisas, entonces prueba {A(c)} para algún individuo concreto. Una prueba de existencia siempre trae a su testigo.' }
    ]),
    T('Lo que vale y lo que no', [
      { say: 'De las leyes que conectan los cuantificadores con la negación, unas direcciones sobreviven y otras se pierden: las que fabricarían un testigo de la nada.',
        fig: table(['Se puede probar', 'No se puede probar'], [['{∃x¬Fx→¬∀xFx}', '{¬∀xFx→∃x¬Fx}'], ['{¬∃xFx↔∀x¬Fx}', '{∀x¬¬Fx→¬¬∀xFx}'], ['{∃x¬¬Fx→¬¬∃xFx}', '{¬¬∃xFx→∃x¬¬Fx}'], ['{¬¬∀xFx→∀x¬¬Fx}', '{∀x(Fx∨¬Fx)}']]) },
      { say: 'Fíjate en el patrón: lo que <i>niega</i> una existencia se puede probar; lo que <i>afirma</i> una existencia a partir de una negación, no. En los retos siguientes vas a recorrer el lado bueno de la tabla.', mood: 'neutral' }
    ]),
    P('Ninguno, luego todos no', ['¬∃xFx'], '∀x¬Fx', 'intfo', {
      intro: 'Esta ley ya la probaste en el Bosque. Mírala de nuevo: no usa {¬¬E}, así que también vale aquí.',
      hints: ['Supón {Fa} para un individuo cualquiera.', 'Con {∃I} obtienes {∃xFx}, que choca con la premisa. Cierra con {¬I}.', 'Tienes {¬Fa} y {a} no aparece en la premisa: aplica {Gen}.'],
      sol: [['H', 'Fa'], ['∃I', [2], '∃xFx'], ['¬E', [3, 1]], ['¬I'], ['Gen', [5], '∀x¬Fx']] }),
    P('Todos no, luego ninguno', ['∀x¬Fx'], '¬∃xFx', 'intfo', {
      intro: 'La dirección contraria. Para refutar un existencial, supón que hay testigo y llévalo al absurdo.',
      hints: ['Supón {∃xFx}. Dentro, supón la instancia {Fa}.', 'Aplica {∀E} a la premisa con el nombre {a}: obtienes {¬Fa}. Contradicción.', 'El {⊥} no menciona a {a}: sal con {∃E} y cierra con {¬I}.'],
      sol: [['H', '∃xFx'], ['H', 'Fa'], ['∀E', [1], '¬Fa'], ['¬E', [3, 4]], ['∃E', [2]], ['¬I']] }),
    P('El testigo se reparte', ['∃x(Fx∧Gx)'], '∃xFx∧∃xGx', 'intfo', {
      intro: 'Un mismo testigo sirve para dos existenciales.',
      hints: ['Supón la instancia {Fa∧Ga}.', 'Separa con {∧E} y aplica {∃I} a cada parte.', 'Une los dos existenciales con {∧I} y sal con {∃E}.'],
      sol: [['H', 'Fa∧Ga'], ['∧E', [2], 'Fa'], ['∃I', [3], '∃xFx'], ['∧E', [2], 'Ga'], ['∃I', [5], '∃xGx'], ['∧I', [4, 6], '∃xFx∧∃xGx'], ['∃E', [1]]] }),
    P('Del método al testigo', ['∀x(Fx→Gx)'], '∃xFx→∃xGx', 'intfo', {
      intro: 'Un universal es un método. Aplícaselo al testigo y tendrás un testigo nuevo.',
      hints: ['Supón {∃xFx} y, dentro, la instancia {Fa}.', 'Con {∀E} y {MP} obtienes {Ga}; luego {∃I}.', 'Sal con {∃E} y cierra con {TD}.'],
      sol: [['H', '∃xFx'], ['H', 'Fa'], ['∀E', [1], 'Fa→Ga'], ['MP', [4, 3]], ['∃I', [5], '∃xGx'], ['∃E', [2]], ['TD']] }),
    P('Testigo bajo doble negación', ['∃x¬¬Fx'], '¬¬∃xFx', 'intfo', {
      intro: 'La doble negación puede salir del existencial hacia fuera. Hacia dentro, no.',
      hints: ['Supón {¬∃xFx} y, dentro, la instancia {¬¬Fa}.', 'Para contradecir {¬¬Fa} necesitas {¬Fa}: supón {Fa}, usa {∃I} y cierra con {¬I}.', 'Con {⊥} sal por {∃E} y termina con {¬I}.'],
      sol: [['H', '¬∃xFx'], ['H', '¬¬Fa'], ['H', 'Fa'], ['∃I', [4], '∃xFx'], ['¬E', [5, 2]], ['¬I'], ['¬E', [7, 3]], ['∃E', [1]], ['¬I']] }),
    P('La doble negación baja', ['¬¬∀xFx'], '∀x¬¬Fx', 'intfo', {
      intro: 'Del universal doblemente negado a cada caso. La vuelta no es constructiva.',
      hints: ['Supón {¬Fa}. Quieres contradecir la premisa, así que necesitas {¬∀xFx}.', 'Dentro, supón {∀xFx}: con {∀E} obtienes {Fa}. Contradicción y {¬I}.', 'Otra contradicción con la premisa, {¬I} para obtener {¬¬Fa}, y {Gen}.'],
      sol: [['H', '¬Fa'], ['H', '∀xFx'], ['∀E', [3], 'Fa'], ['¬E', [4, 2]], ['¬I'], ['¬E', [6, 1]], ['¬I'], ['Gen', [8], '∀x¬¬Fx']] }),
    T('Mundos que crecen', [
      { say: 'En los modelos de Kripke del intuicionismo de primer orden, cada estado de conocimiento tiene su propio <b>dominio</b> de individuos, y los dominios solo crecen: lo ya construido no desaparece, pero pueden aparecer individuos nuevos.', mood: 'neutral' },
      { say: '{∀xA} vale en un estado si {A} vale de todos los individuos de ese estado <i>y de todos los estados posteriores</i>. {∃xA} vale si {A} vale ya de algún individuo presente.',
        fig: { k: 'kripke', h: 110, w: [{ id: 'w0', x: 10, y: 30, t: 'existe a' }, { id: 'w1', x: 196, y: 30, t: 'a, b · Fa' }], e: [['w0', 'w1']],
          cap: 'En w0 vale {¬∀xFx}: b nunca llega a ser F. Pero no vale {∃x¬Fx}: el único individuo de w0 es a, y {Fa} se prueba en w1.' } },
      { say: 'Ese modelo es un contraejemplo de {¬∀xFx→∃x¬Fx}. El clásico razona «si no todos, alguno no»; el constructivista pregunta «¿cuál?», y en w0 no hay respuesta.' }
    ]),
    Q('¿Con testigo o sin él?', [
      { q: '¿Se puede probar {¬∀xFx→∃x¬Fx} en lógica intuicionista?', opts: ['Sí', 'No'], ok: 1,
        why: 'Saber que no todos son F no entrega ningún individuo concreto que no lo sea. El modelo de los dos estados lo refuta.' },
      { q: '¿Y {∃x¬Fx→¬∀xFx}?', opts: ['Sí', 'No'], ok: 0,
        why: 'Aquí el testigo viene en la premisa: basta aplicarle el universal para llegar al absurdo. Lo probaste en el Mundo 5.' },
      { q: '¿Y {∀x¬¬Fx→¬¬∀xFx}?', opts: ['Sí', 'No'], ok: 1,
        why: 'Es el «desplazamiento de la doble negación». Que cada individuo sea irrefutablemente F no da un método uniforme para todos; falla en modelos con infinitos estados.' },
      { q: 'Si se prueba {∃xA(x)} sin premisas, ¿qué garantiza la lógica intuicionista?', opts: ['Nada más', 'Que se puede probar {A(c)} para algún c concreto', 'Que {A} vale de todos los individuos'], ok: 1,
        why: 'Es la <b>propiedad de la existencia</b>, hermana de la propiedad de la disyunción. En lógica clásica falla: se prueba {∃x(Fx→∀yFy)} sin poder señalar a nadie.' }
    ]),
    P('Existencia irrefutable', ['¬¬∃xFx', '∀x(Fx→Gx)'], '¬¬∃xGx', 'intfo', {
      boss: true,
      intro: 'El jefe del jardín. No tienes testigo, solo la garantía de que no se puede refutar que lo haya. Aun así algo se puede transportar.',
      hints: ['Supón {¬∃xGx}. Para contradecir la primera premisa necesitas {¬∃xFx}.', 'Supón {∃xFx} y su instancia {Fa}: con {∀E}, {MP} y {∃I} llegas a {∃xGx}. Contradicción; sal con {∃E}.', 'Cierra con {¬I} para obtener {¬∃xFx}, contradice la premisa y termina con {¬I}.'],
      sol: [['H', '¬∃xGx'], ['H', '∃xFx'], ['H', 'Fa'], ['∀E', [2], 'Fa→Ga'], ['MP', [6, 5]], ['∃I', [7], '∃xGx'], ['¬E', [8, 3]], ['∃E', [4]], ['¬I'], ['¬E', [11, 1]], ['¬I']] }),
    V('El buscador de testigos', 'int', { cmp: 'cl', syms: '¬∧∨→↔⊥∀∃', goals: ['valid', 'gap', 'own'],
      intro: 'Con cuantificadores, los estados de conocimiento tienen además individuos. El buscador compara la lógica intuicionista de primer orden con la clásica y, cuando hay contramodelo, te lo dibuja.',
      outro: 'Algunos argumentos solo se refutan con infinitos estados, como {∀x¬¬Fx ⊢ ¬¬∀xFx}. Entonces el buscador reconoce que no puede decidir.',
      ex: [[['¬∀xFx'], '∃x¬Fx', 'invalid'], [['∃x¬Fx'], '¬∀xFx', 'valid'], [['¬¬∃xFx'], '∃xFx', 'invalid'], [[], '∀x(Fx∨¬Fx)', 'invalid'], [['∃x(Fx∧Gx)'], '∃xFx∧∃xGx', 'valid'], [['¬¬∃xFx', '∀x(Fx→Gx)'], '¬¬∃xGx', 'valid'], [['∀x¬¬Fx'], '¬¬∀xFx', 'unknown']] })
  ]
};

/* ============ MUNDO 8 · paraconsistente de primer orden ============ */
const w8 = {
  k: 8, name: 'Abismo de las Paradojas', logic: 'Lógica paraconsistente de primer orden (LP)', badge: '¬∀',
  intro: 'En el fondo del abismo hay objetos que son y no son a la vez. La lógica aguanta.',
  stages: [
    T('Objetos contradictorios', [
      { say: 'Bajamos un nivel más. En la versión de primer orden de LP, un predicado tiene una <b>extensión</b> (los individuos de los que es verdadero) y una <b>antiextensión</b> (aquellos de los que es falso). Entre las dos cubren todo el dominio, pero pueden solaparse.' },
      { say: 'Si un individuo está en las dos, {Fa} vale A: es verdadera y falsa. Los cuantificadores se calculan como una conjunción y una disyunción grandes: {∀xFx} toma el menor valor entre todos los individuos y {∃xFx}, el mayor.',
        fig: table(['{Fa}', '{Fb}', '{∀xFx}', '{∃xFx}'], [['V', 'V', 'V', 'V'], ['V', 'A', 'A', 'V'], ['A', 'F', 'F', 'A'], ['F', 'F', 'F', 'F']]) },
      { say: 'Un ejemplo célebre es el conjunto de Russell, {R}: el de todos los conjuntos que no se pertenecen a sí mismos. La teoría ingenua de conjuntos prueba que {R} se pertenece y que no se pertenece. Con lógica clásica, la teoría entera estalla. Con LP, la contradicción queda encerrada en {R}.', mood: 'neutral' },
      { say: 'Un argumento es válido si conserva los valores designados (V y A) en todo dominio y toda interpretación. Vas a comprobar que el silogismo disyuntivo sigue fallando, ahora con cuantificadores.' }
    ]),
    M('Un individuo paradójico', 'LP', ['∀x(Fx∨Gx)', '∃x¬Fx'], '∃xGx', { dom: ['a', 'b'],
      intro: 'El dominio tiene dos individuos, a y b. Busca valores que hagan designadas las premisas y no la conclusión.',
      outro: 'Basta un individuo paradójico: si {Fa} vale A, a cumple {Fx∨Gx} y también {¬Fx}, aunque nada sea G.' }),
    T('Reglas para cuantificar en LP', [
      { say: 'En el cálculo de LP entran las cuatro reglas de los cuantificadores, como en el Bosque: {Gen}, {∀E}, {∃I} y {∃E}. Siguen fuera {⊥}, {¬I} y {¬E}, y sigue sin haber modus ponens.' },
      { say: 'Como no hay reducción al absurdo, la negación de un cuantificador se maneja con una regla propia, <b>QN</b>, igual que {DeM} maneja la de las conectivas.',
        fig: table(['Regla', 'Qué permite'], [['{QN}', 'pasar de {¬∀xA} a {∃x¬A}, y al revés'], ['{QN}', 'pasar de {¬∃xA} a {∀x¬A}, y al revés'], ['{LEM}', 'escribir {A∨¬A} para cualquier fórmula, también con nombres']]) },
      { say: 'Compara tres mundos. De {¬∀xFx} a {∃x¬Fx}: en la lógica clásica fue el jefe del Bosque, once líneas con {¬¬E}; en la intuicionista no se puede probar; en LP es un solo paso de {QN}. Cada lógica reparte de otra forma lo fácil y lo imposible.' }
    ]),
    P('Un solo paso', ['¬∀xFx'], '∃x¬Fx', 'lpq', { sys: 'LP',
      intro: 'El jefe del Bosque, resuelto de un golpe.',
      hints: ['Selecciona la premisa.', 'Pulsa {QN}.'],
      sol: [['QN', [1]]] }),
    P('Nadie, luego este tampoco', ['¬∃xFx'], '¬Fa', 'lpq', { sys: 'LP',
      intro: 'Primero mueve la negación hacia dentro; después baja al caso particular.',
      hints: ['{QN} sobre la premisa da {∀x¬Fx}.', 'Aplica {∀E} y elige el nombre {a}.'],
      sol: [['QN', [1]], ['∀E', [2], '¬Fa']] }),
    P('Tercero excluido para todos', [], '∀x(Fx∨¬Fx)', 'lpq', { sys: 'LP',
      intro: 'Lo que el intuicionista no puede probar, en LP sale en dos pasos.',
      hints: ['Pulsa {LEM} y escribe la fórmula {Fa} con el teclado del cuadro.', 'Tienes {Fa∨¬Fa} y {a} es arbitrario: aplica {Gen}.'],
      sol: [ax('LEM', { A: 'Fa' }), ['Gen', [1], '∀x(Fx∨¬Fx)']] }),
    P('Nada es contradictorio', [], '¬∃x(Fx∧¬Fx)', 'lpq', { sys: 'LP',
      intro: 'LP demuestra que no hay objetos contradictorios… y aun así admite modelos donde los hay. Las dos cosas valen a la vez.',
      hints: ['Pulsa {LEM} y escribe {¬Fa}: obtienes {¬Fa∨¬¬Fa}.', '{DeM} lo convierte en {¬(Fa∧¬Fa)}. Generaliza con {Gen}.', 'Termina con {QN}.'],
      sol: [ax('LEM', { A: '¬Fa' }), ['DeM', [1]], ['Gen', [2], '∀x¬(Fx∧¬Fx)'], ['QN', [3]]] }),
    P('Un objeto inconsistente', ['∃x(Fx∧¬Fx)'], '∃xFx∧¬∀xFx', 'lpq', { sys: 'LP',
      intro: 'De un objeto contradictorio no se sigue cualquier cosa. Se sigue justo esto.',
      hints: ['Supón la instancia {Fa∧¬Fa} y sepárala con {∧E}.', 'De {Fa}, {∃I}. De {¬Fa}, {∃I} y luego {QN} para obtener {¬∀xFx}.', 'Une con {∧I} y sal con {∃E}.'],
      sol: [['H', 'Fa∧¬Fa'], ['∧E', [2], 'Fa'], ['∃I', [3], '∃xFx'], ['∧E', [2], '¬Fa'], ['∃I', [5], '∃x¬Fx'], ['QN', [6]], ['∧I', [4, 7], '∃xFx∧¬∀xFx'], ['∃E', [1]]] }),
    P('Silogismo disyuntivo con salvedad', ['∀x(Fx∨Gx)', '¬Fa'], 'Ga∨(Fa∧¬Fa)', 'lpq', { sys: 'LP',
      intro: 'Como en la Caverna: o bien {Ga}, o bien a es un objeto contradictorio.',
      hints: ['{∀E} con el nombre {a} da {Fa∨Ga}. Razona por casos.', 'Caso {Fa}: únela con {¬Fa} por {∧I} y pasa a la conclusión con {∨I}. Cierra la subprueba.', 'Caso {Ga}: {∨I} directa, y {∨E}.'],
      sol: [['∀E', [1], 'Fa∨Ga'], ['H', 'Fa'], ['∧I', [4, 2], 'Fa∧¬Fa'], ['∨I', [5], 'Ga∨(Fa∧¬Fa)', 'Ga'], ['C'], ['H', 'Ga'], ['∨I', [7], 'Ga∨(Fa∧¬Fa)', 'Fa∧¬Fa'], ['∨E', [3]]] }),
    Q('Leyes que resisten', [
      { q: 'En LP de primer orden, ¿es válido pasar de {∃x(Fx∧¬Fx)} a {∀xGx}?', opts: ['Sí, por explosión', 'No: la contradicción no contagia a los demás predicados'], ok: 1,
        why: 'Un individuo puede ser F y no F mientras todo lo demás sigue su curso. Eso es justamente ser paraconsistente.' },
      { q: '¿Cuál de estas es un teorema de LP?', opts: ['{∃x(Fx∧¬Fx)}', '{¬∃x(Fx∧¬Fx)}', 'Ninguna de las dos'], ok: 1,
        why: 'LP tiene los mismos teoremas que la lógica clásica, también con cuantificadores. Eso no impide que {∃x(Fx∧¬Fx)} sea verdadera en algunas interpretaciones.' },
      { q: 'En un dominio con solo a y b, {Fa} vale A y {Fb} vale V. ¿Cuánto vale {∀xFx}?', opts: ['V', 'A', 'F'], ok: 1,
        why: 'El universal toma el menor valor. Es designado, así que se acepta {∀xFx}, y también {¬∀xFx}.' }
    ]),
    P('Silogismo disyuntivo cuantificado', ['∀x(Fx∨Gx)', '∃x¬Fx'], '∃x(Gx∨(Fx∧¬Fx))', 'lpq', { sys: 'LP', boss: true,
      intro: 'El jefe del abismo: el argumento que viste fallar, reparado con su salvedad y con cuantificadores.',
      hints: ['Supón la instancia {¬Fa}. Dentro, {∀E} con {a} da {Fa∨Ga}.', 'Razona por casos como en el reto anterior hasta obtener {Ga∨(Fa∧¬Fa)}.', 'Generaliza con {∃I} sobre todas las apariciones de {a} y sal con {∃E}.'],
      sol: [['H', '¬Fa'], ['∀E', [1], 'Fa∨Ga'], ['H', 'Fa'], ['∧I', [5, 3], 'Fa∧¬Fa'], ['∨I', [6], 'Ga∨(Fa∧¬Fa)', 'Ga'], ['C'], ['H', 'Ga'], ['∨I', [8], 'Ga∨(Fa∧¬Fa)', 'Fa∧¬Fa'], ['∨E', [4]],
        ['∃I', [10], '∃x(Gx∨(Fx∧¬Fx))'], ['∃E', [2]]] }),
    V('La sonda del abismo', 'lp', { cmp: 'cl', syms: '¬∧∨→↔∀∃', goals: ['valid', 'gap', 'own'],
      intro: 'La sonda evalúa argumentos con cuantificadores en LP y en la lógica clásica. Si encuentra un contraejemplo, te enseña cuánto vale cada predicado para cada individuo.',
      outro: 'Una contradicción en un individuo no contagia a los demás. Así es como LP encierra una paradoja.',
      ex: [[['∀x(Fx∨Gx)', '∃x¬Fx'], '∃xGx', 'invalid'], [['¬∀xFx'], '∃x¬Fx', 'valid'], [[], '¬∃x(Fx∧¬Fx)', 'valid'], [['∃x(Fx∧¬Fx)'], '∀xGx', 'invalid'], [['∀x(Fx→Gx)', 'Fa'], 'Ga', 'invalid'], [['∀x(Fx∨Gx)', '¬Fa'], 'Ga∨(Fa∧¬Fa)', 'valid']] })
  ]
};

/* ============ MUNDO 9 · teoremas de incompletud ============ */
const w9 = {
  k: 9, name: 'Torre de Gödel', logic: 'Aritmética formal y teoremas de incompletud', badge: '⌜G⌝',
  intro: 'Desde lo alto de esta torre la lógica se mira a sí misma. Sube con calma: cada piso prepara el siguiente.',
  stages: [
    T('El programa de Hilbert', [
      { say: 'Hacia 1920 David Hilbert propuso asegurar toda la matemática de una vez: encerrarla en un <b>sistema formal</b>, con axiomas y reglas tan precisos que una máquina pudiera revisar cada prueba. Es el tipo de sistema con el que has jugado en todos los mundos anteriores.', mood: 'neutral' },
      { say: 'El sistema ideal debía ser consistente y completo, y su consistencia debía poder demostrarse con métodos elementales, fuera de toda duda.',
        fig: table(['Propiedad', 'Qué pide'], [['consistente', 'nunca prueba {A} y {¬A}'], ['completo', 'para toda oración {A}, prueba {A} o prueba {¬A}'], ['efectivo', 'un procedimiento mecánico revisa si una prueba es correcta']]) },
      { say: 'En 1931 Kurt Gödel, con 25 años, mostró que ese ideal es inalcanzable para cualquier sistema capaz de expresar la aritmética. Para entender sus dos teoremas hay que subir cinco pisos: aritmética formal, numeración de Gödel, demostrabilidad, autorreferencia y, al final, las pruebas.', mood: 'neutral' }
    ]),
    T('La aritmética formal', [
      { say: 'Nuestro sistema hablará de los números naturales. Su lenguaje tiene un nombre, {0}; una función «sucesor», {S}; suma y producto; la igualdad; y toda la lógica de primer orden. No hay cifras: {S0} es el uno, {SS0} el dos, {SSS0} el tres.',
        fig: table(['Símbolo', 'Significa'], [['{0}', 'el cero'], ['{S}', 'el sucesor: el número siguiente'], ['{+}  {×}', 'suma y producto'], ['{SSS0}', 'el numeral del 3']]) },
      { say: 'Los axiomas básicos son siete y forman la <b>aritmética de Robinson</b>, llamada Q. Son tan modestos que apenas dicen cómo se suma y se multiplica.',
        fig: table(['Axiomas de Q'], [['{∀x ¬Sx=0}'], ['{∀x∀y(Sx=Sy→x=y)}'], ['{∀x(x=0∨∃y x=Sy)}'], ['{∀x x+0=x}'], ['{∀x∀y x+Sy=S(x+y)}'], ['{∀x x×0=0}'], ['{∀x∀y x×Sy=(x×y)+x}']]) },
      { say: 'La <b>aritmética de Peano</b>, PA, añade el esquema de <b>inducción</b>: si algo vale del cero y pasa de cada número al siguiente, vale de todos. Con PA se prueba prácticamente toda la teoría de números habitual.' },
      { say: 'Dos nociones que no hay que confundir nunca. Una oración es <b>verdadera</b> si se cumple en los números naturales de verdad, el modelo estándar {ℕ}. Es <b>demostrable</b> en una teoría T si hay una prueba formal a partir de los axiomas de T; se escribe {T ⊢ A}. Todo el asunto de esta torre es la distancia entre ambas.' }
    ]),
    Q('Números y teorías', [
      { q: '¿Cómo se escribe el número 3 en el lenguaje de la aritmética?', opts: ['{3}', '{SSS0}', '{S+S+S}'], ok: 1,
        why: 'El lenguaje no tiene cifras: solo {0} y el sucesor. El numeral del 3 es {SSS0}.' },
      { q: '¿Qué añade PA a la aritmética de Robinson?', opts: ['El producto', 'El esquema de inducción', 'Los números negativos'], ok: 1,
        why: 'Q ya tiene suma y producto. La inducción es lo que permite probar leyes generales, como que la suma es conmutativa.' },
      { q: '{T ⊢ A} significa que…', opts: ['{A} es verdadera en los números naturales', 'hay una prueba formal de {A} a partir de los axiomas de T', '{A} es un axioma de T'], ok: 1,
        why: 'Demostrable y verdadera son nociones distintas: una es sintáctica y depende de T; la otra es semántica y depende de {ℕ}.' }
    ]),
    T('La numeración de Gödel', [
      { say: 'Primera idea genial: los números pueden hablar de fórmulas si a cada fórmula se le asigna un número. Se empieza dando un código a cada símbolo.',
        fig: Object.assign(table(['Símbolo', '{0}', '{S}', '{+}', '{×}', '{=}', '{(}', '{)}', '{¬}', '{→}', '{∀}', '{x}'], [['Código', '1', '2', '3', '4', '5', '6', '7', '8', '9', '10', '11']]), { tight: true }) },
      { say: 'Una fórmula es una fila de símbolos. Para convertirla en un solo número se usan los primos en orden, 2, 3, 5, 7…, y cada uno se eleva al código del símbolo que ocupa su lugar. La fórmula {0=0} tiene códigos 1, 5, 1, así que su número es 2<sup>1</sup> · 3<sup>5</sup> · 5<sup>1</sup> = 2430.' },
      { say: 'Como cada número se descompone en primos de una única manera, el camino de vuelta también funciona: del número se recuperan los exponentes y, con ellos, la fórmula. Nada se pierde.' },
      { say: 'El mismo truco se repite un piso más arriba: una <b>prueba</b> es una fila de fórmulas, así que también recibe su número. Escribiremos {⌜A⌝} para el número de Gödel de {A}. Los detalles del código no importan; lo que importa es que codificar y decodificar sean operaciones mecánicas.' }
    ]),
    GN('Tu primer número de Gödel', 'enc', ['0', '=', '0'], {
      intro: 'Codifica la fórmula {0=0}: elige el exponente de cada primo según la tabla de códigos.',
      outro: 'El número de Gödel de {0=0} es 2430. Una oración verdadera sobre el cero, convertida en un número.' }),
    GN('De vuelta a los símbolos', 'dec', ['S', '0', '=', 'S', '0'], {
      intro: 'Ahora al revés. Este número ya está descompuesto en primos: lee cada exponente y elige el símbolo que le corresponde.',
      outro: 'El número 20 212 500 es la fórmula {S0=S0}: «uno es igual a uno».' }),
    GN('Una fórmula con negación', 'enc', ['¬', '0', '=', 'S', '0'], {
      intro: 'Codifica {¬0=S0}, «cero no es uno». Son cinco símbolos, así que hacen falta los cinco primeros primos.',
      outro: 'Los números crecen muy rápido, pero eso no importa: lo esencial es que cada fórmula tiene el suyo y que se puede recuperar.' }),
    T('La sintaxis se vuelve aritmética', [
      { say: 'Segunda idea: como las fórmulas son números, las propiedades de las fórmulas son propiedades de números. «Ser una fórmula bien formada», «ser un axioma», «seguirse por modus ponens» se convierten en relaciones aritméticas entre códigos.' },
      { say: 'La más importante es la relación de prueba: {Prf(m, n)} vale cuando m es el código de una prueba, en T, de la fórmula cuyo código es n. Comprobarla es mecánico: se decodifica m y se revisa línea por línea. Por eso exigimos que T sea <b>efectivamente axiomatizada</b>.' },
      { say: 'Y aquí entra la aritmética: toda relación que se comprueba mecánicamente es <b>representable</b> en Q. Con sus propias fórmulas, T puede revisar pruebas de T.',
        fig: table(['Si…', 'entonces…'], [['m es una prueba de la fórmula n', '{T ⊢ Prf(m, n)}'], ['m no es una prueba de la fórmula n', '{T ⊢ ¬Prf(m, n)}']]) },
      { say: 'Con ella se define el <b>predicado de demostrabilidad</b>: {Prov(n)} dice «existe un m tal que {Prf(m, n)}». Ojo con la asimetría: revisar una prueba dada es mecánico, pero buscar una prueba puede no terminar nunca. {Prov} es de la forma {Σ₁}: un existencial delante de algo comprobable.' },
      { say: 'De ahí sale una propiedad que usaremos: si T demuestra {A}, entonces T demuestra {Prov(⌜A⌝)}. Basta tomar el código de la prueba y comprobarlo. En general, T demuestra toda oración {Σ₁} verdadera.' }
    ]),
    Q('Pruebas como números', [
      { q: '¿Por qué de un número de Gödel se puede recuperar la fórmula original?', opts: ['Porque los números son infinitos', 'Porque la descomposición en primos es única', 'Porque T es completa'], ok: 1,
        why: 'Los exponentes de los primos, leídos en orden, son los códigos de los símbolos.' },
      { q: '¿En qué se diferencian {Prf(m, n)} y {Prov(n)}?', opts: ['{Prf} se comprueba mecánicamente; {Prov} exige buscar una prueba que quizá no exista', '{Prf} habla de fórmulas y {Prov} de números', 'En nada'], ok: 0,
        why: 'Revisar una prueba dada siempre termina. Buscar una prueba entre todos los números puede no terminar nunca.' },
      { q: 'Si T demuestra {A}, ¿qué demuestra también T?', opts: ['{Prov(⌜A⌝)}', '{¬Prov(⌜A⌝)}', '{Prov(⌜¬A⌝)}'], ok: 0,
        why: 'Hay una prueba con un código concreto m, y T puede comprobar {Prf(m, ⌜A⌝)}.' }
    ]),
    T('El lema diagonal', [
      { say: 'Tercera idea, la más sutil: la <b>autorreferencia</b>. Una oración no puede contener escrito su propio número de Gödel, porque sería más larga que ella misma. Hay que llegar por un rodeo.', mood: 'neutral' },
      { say: 'El rodeo es la <b>diagonalización</b>. Toma una fórmula con una variable libre, {B(x)}, y sustituye la variable por el numeral del código de la propia fórmula: obtienes {B(⌜B⌝)}. Esta operación sobre códigos es mecánica, así que T puede hablar de ella.' },
      { say: 'Una versión en castellano, debida a Quine: «da una falsedad cuando va precedida de su propia cita» da una falsedad cuando va precedida de su propia cita. La oración habla de una expresión, y al aplicarle la operación indicada se obtiene la oración misma.' },
      { say: '<b>Lema diagonal</b>: para cualquier fórmula {A(x)} existe una oración {D} tal que T demuestra {D ↔ A(⌜D⌝)}. Es decir, {D} dice de sí misma «tengo la propiedad A». No es magia ni circularidad: es una sustitución bien calculada.', mood: 'neutral' }
    ]),
    Q('Autorreferencia', [
      { q: '¿Qué garantiza el lema diagonal?', opts: ['Que toda oración es verdadera o falsa', 'Que para cada propiedad {A(x)} hay una oración que dice «yo tengo A»', 'Que toda fórmula tiene un número de Gödel'], ok: 1,
        why: 'Y lo garantiza para cualquier propiedad expresable: ser demostrable, no serlo, tener un código par…' },
      { q: 'Si aplicamos el lema a la propiedad «no ser demostrable», obtenemos una oración que dice…', opts: ['«Soy falsa»', '«No soy demostrable»', '«Soy demostrable»'], ok: 1,
        why: 'Esa es la oración de Gödel. La del mentiroso, «soy falsa», necesitaría un predicado de verdad, y ese no existe dentro de la aritmética.' }
    ]),
    T('La oración de Gödel', [
      { say: 'Ya están todas las piezas. Aplica el lema diagonal a la propiedad «no ser demostrable», {¬Prov(x)}. Obtienes una oración {G} tal que T demuestra {G ↔ ¬Prov(⌜G⌝)}.' },
      { say: '{G} dice: «no soy demostrable en T». Se parece a la paradoja del mentiroso, pero hay una diferencia decisiva: no habla de <i>verdad</i>, sino de <i>demostrabilidad</i>, y esa sí es una noción aritmética. Por eso {G} no es una paradoja: es una oración aritmética perfectamente legítima.' },
      { say: '<b>Primer teorema de incompletud</b>: si T es consistente, efectivamente axiomatizada y contiene la aritmética básica, hay oraciones que T no puede probar ni refutar. {G} es una de ellas. Hay dos caminos para demostrarlo, y vas a recorrer los dos.',
        fig: table(['Camino', 'Supone', 'Usa'], [['semántico', 'que T solo demuestra verdades', 'la noción de verdad en {ℕ}'], ['sintáctico', 'que T es consistente, y algo más', 'solo pruebas, sin hablar de verdad']]) }
    ]),
    T('La prueba semántica', [
      { say: 'Empecemos por el camino corto. Supón que T es <b>correcta</b>: todo lo que demuestra es verdadero en {ℕ}. Nos preguntamos si T puede demostrar {G}.', mood: 'neutral' },
      { say: 'Si T demostrara {G}, entonces {G} sería verdadera, por corrección. Pero {G} dice que no es demostrable: sería demostrable y, a la vez, verdadero que no lo es. Contradicción. Luego T no demuestra {G}.' },
      { say: 'Y entonces {G} es <b>verdadera</b>, porque dice exactamente eso: que no es demostrable. Su negación {¬G} es falsa, así que T, que solo demuestra verdades, tampoco demuestra {¬G}. Conclusión: {G} es verdadera e indecidible en T.' },
      { say: 'El argumento es limpio, pero usa la noción de verdad, que no pertenece al sistema. En el reto siguiente lo reconstruyes con dos letras: {G}, «la oración de Gödel es verdadera», y {D}, «T demuestra la oración de Gödel».' }
    ]),
    P('Verdadera e indemostrable', ['G↔¬D', 'D→G'], 'G∧¬D', 'cl', {
      intro: 'La primera premisa es lo que dice {G}; la segunda, que T es correcta. Demuestra que {G} es verdadera y que T no la demuestra.',
      hints: ['Supón {D}. Con la segunda premisa obtienes {G}; con la primera y {G}, {¬D}. Contradicción.', 'Cierra con {¬I}: ya tienes {¬D}.', 'Con {↔E} sobre la primera premisa y {¬D} obtienes {G}. Une con {∧I}.'],
      sol: [['H', 'D'], ['MP', [2, 3]], ['↔E', [1, 4], '¬D'], ['¬E', [3, 5]], ['¬I'], ['↔E', [1, 7], 'G'], ['∧I', [8, 7], 'G∧¬D']] }),
    T('La prueba sintáctica', [
      { say: 'Gödel quiso un argumento que no hablara de verdad, solo de pruebas. La hipótesis mínima es que T sea <b>consistente</b>. Primera mitad: T no demuestra {G}.' },
      { say: 'Supón que T demuestra {G}. Entonces existe una prueba, con su código, y T puede comprobarla: T demuestra {Prov(⌜G⌝)}. Pero {G} equivale en T a {¬Prov(⌜G⌝)}, así que T demuestra una oración y su negación.',
        fig: table(['Paso', 'Por qué'], [['{T ⊢ G}', 'es el supuesto'], ['{T ⊢ Prov(⌜G⌝)}', 'T comprueba esa prueba'], ['{T ⊢ ¬Prov(⌜G⌝)}', 'por lo que dice {G}'], ['T es inconsistente', 'demuestra una oración y su negación']]) },
      { say: 'Segunda mitad: T no demuestra {¬G}. Aquí Gödel necesitó algo más fuerte, la <b>{ω}-consistencia</b>: T no demuestra «existe un número con la propiedad A» mientras refuta A de cada número concreto, uno por uno.' },
      { say: 'Supón que T demuestra {¬G}, es decir, {Prov(⌜G⌝)}: «existe una prueba de G». Por la primera mitad no hay tal prueba, así que para cada número m, T demuestra {¬Prf(m, ⌜G⌝)}. T afirma que existe lo que refuta caso por caso: no es {ω}-consistente.' },
      { say: 'En 1936 J. B. Rosser eliminó esa hipótesis extra con una oración más astuta: «si hay una prueba de mí, hay otra más corta de mi negación». Con ella basta la simple consistencia: toda teoría consistente, efectiva y con aritmética básica es incompleta.' }
    ]),
    P('T no demuestra G', ['D→R', '¬(D∧R)'], '¬D', 'cl', {
      intro: '{D}: «T demuestra G». {R}: «T refuta G», es decir, demuestra su negación. La primera premisa resume el argumento de la página anterior; la segunda dice que T es consistente.',
      hints: ['Supón {D}.', 'Con {MP} obtienes {R}; únelas con {∧I}.', 'Eso contradice la consistencia: {¬E} y {¬I}.'],
      sol: [['H', 'D'], ['MP', [1, 3]], ['∧I', [3, 4], 'D∧R'], ['¬E', [5, 2]], ['¬I']] }),
    P('T no refuta G', ['(R∧¬D)→¬W', 'W', '¬D'], '¬R', 'cl', {
      intro: '{W}: «T es {ω}-consistente». Si T refutara {G} sin demostrarla, dejaría de serlo. Y ya sabes que T no demuestra {G}.',
      hints: ['Supón {R}.', 'Une {R} con {¬D} por {∧I} y aplica {MP}: obtienes {¬W}.', 'Contradice a {W}: {¬E} y {¬I}.'],
      sol: [['H', 'R'], ['∧I', [4, 3], 'R∧¬D'], ['MP', [1, 5]], ['¬E', [2, 6]], ['¬I']] }),
    T('Qué dice y qué no dice', [
      { say: 'El teorema se cita mucho y mal. Dice: toda teoría <b>consistente</b>, <b>efectivamente axiomatizada</b> y que contenga la aritmética de Robinson es <b>incompleta</b>. Las tres condiciones hacen falta.',
        fig: table(['Si falta…', 'Ejemplo', 'Resultado'], [['la aritmética', 'la aritmética de Presburger, solo con suma', 'es completa y decidible'], ['la axiomatización efectiva', 'tomar como axiomas todas las verdades de {ℕ}', 'es completa, pero nadie puede revisar sus pruebas'], ['la consistencia', 'una teoría inconsistente', 'lo demuestra todo']]) },
      { say: 'No dice que {G} sea indemostrable «en absoluto». {G} se demuestra en teorías más fuertes, por ejemplo en T más el axioma {G}. Pero esa teoría nueva tiene su propia oración de Gödel. La incompletud no se cura añadiendo axiomas.' },
      { say: 'Tampoco contradice el <b>teorema de completitud</b> que Gödel había probado en 1929. Aquel dice que la <i>lógica</i> es completa: lo que vale en todos los modelos se puede demostrar. Como T no demuestra {G}, hay modelos de T donde {G} es falsa: modelos <b>no estándar</b>, con «números» extraños más allá de los naturales.' },
      { say: 'Un pariente cercano es el teorema de <b>Tarski</b>: la verdad aritmética no es definible en la aritmética. Si hubiera una fórmula {True(x)}, el lema diagonal daría una oración que dice «soy falsa», y esa sí es contradictoria. La demostrabilidad es definible; la verdad, no. Por eso no pueden coincidir.' }
    ]),
    Q('Malentendidos', [
      { q: '¿Cuál de estas afirmaciones es correcta?', opts: ['Hay verdades matemáticas que ningún sistema puede demostrar', 'Cada sistema consistente con aritmética deja sin decidir alguna oración, que otro sistema más fuerte sí decide', 'La matemática es inconsistente'], ok: 1,
        why: 'La incompletud es siempre relativa a un sistema. No hay una oración «absolutamente indemostrable».' },
      { q: 'La aritmética de Presburger, que solo tiene suma, es completa y decidible. ¿Contradice eso a Gödel?', opts: ['Sí', 'No: sin producto no puede expresar la numeración de Gödel'], ok: 1,
        why: 'El teorema solo se aplica a teorías que contienen suficiente aritmética, y para eso hacen falta suma y producto.' },
      { q: 'Si a PA le añadimos {G} como axioma nuevo…', opts: ['obtenemos una teoría completa', 'la teoría nueva tiene su propia oración indecidible', 'la teoría se vuelve inconsistente'], ok: 1,
        why: 'La teoría ampliada sigue cumpliendo las tres condiciones, así que el teorema se le aplica otra vez.' },
      { q: 'El teorema de completitud de 1929 y el de incompletud de 1931…', opts: ['se contradicen', 'hablan de cosas distintas: la completitud de la lógica y la incompletud de las teorías aritméticas', 'son el mismo teorema'], ok: 1,
        why: 'La lógica de primer orden demuestra todo lo que vale en todos los modelos. {G} no vale en todos los modelos de T: falla en algunos no estándar.' }
    ]),
    T('El segundo teorema', [
      { say: 'Queda la pregunta de Hilbert: ¿puede T demostrar su propia consistencia? Primero hay que poder decirlo. «T es consistente» se escribe {Con(T)}: es la oración {¬Prov(⌜0=S0⌝)}, «T no demuestra que cero es uno».' },
      { say: 'Ahora mira la primera mitad de la prueba sintáctica: «si T es consistente, T no demuestra G». Ese razonamiento es tan elemental que puede formalizarse <i>dentro</i> de T. El resultado es que T demuestra {Con(T) → ¬Prov(⌜G⌝)}, o sea, {Con(T) → G}.' },
      { say: '<b>Segundo teorema de incompletud</b>: si T es consistente, T no demuestra {Con(T)}. Porque si la demostrara, por modus ponens demostraría {G}, y el primer teorema lo prohíbe. Ninguna teoría razonable certifica su propia consistencia.' },
      { say: 'Para formalizar el razonamiento bastan tres propiedades de {Prov}, las <b>condiciones de derivabilidad</b>. Si lees {□A} como «T demuestra A», son viejas conocidas del Archipiélago.',
        fig: table(['Condición', 'En símbolos modales'], [['si T demuestra {A}, T demuestra {Prov(⌜A⌝)}', 'de {A} se pasa a {□A}'], ['{Prov} respeta el modus ponens', '{□(A→B)→(□A→□B)}'], ['si algo es demostrable, es demostrable que lo es', '{□A→□□A}']]) },
      { say: 'Así que puedes demostrar los dos teoremas en el sistema K4 de Hilbert: los axiomas {K} y {4}, la necesitación y el cálculo proposicional. Cuidado: aquí no está el axioma {T}. Que T demuestre algo no garantiza, <i>dentro de T</i>, que sea verdad. La premisa {□(G↔¬□G)} es el lema diagonal, y {□⊥} significa «T es inconsistente».' }
    ]),
    P('El primer teorema, formalizado', ['□(G↔¬□G)'], '□G→□⊥', 'k4', { sys: 'K4',
      intro: 'Demuestra que si T demuestra {G}, entonces T es inconsistente. Es la primera mitad de la prueba sintáctica, ahora dentro del sistema. Vas a necesitar dos teoremas auxiliares, que se prueban sin depender de nada.',
      hints: ['Supón {□G}. El axioma {4} te da {□□G}. Prueba el teorema {(G↔¬□G)→(G→¬□G)} y aplica {Mon} con la premisa: {□(G→¬□G)}; con {RK} y {□G}, {□¬□G}.', 'Prueba el teorema {□G→(¬□G→⊥)}: supón {□G}, supón {¬□G}, {¬E} y cierra dos veces con {TD}. {Mon} con {□□G} da {□(¬□G→⊥)}.', 'Con {RK} y {□¬□G} obtienes {□⊥}. Cierra con {TD}.'],
      sol: [['H', '□G'], ax('4', { A: 'G' }), ['MP', [3, 2]],
        ['H', 'G↔¬□G'], ['H', 'G'], ['↔E', [5, 6], '¬□G'], ['TD'], ['TD'], ['Mon', [9, 1]], ['RK', [10, 2]],
        ['H', '□G'], ['H', '¬□G'], ['¬E', [12, 13]], ['TD'], ['TD'], ['Mon', [16, 4]], ['RK', [17, 11]], ['TD']] }),
    P('El segundo teorema', ['□(G↔¬□G)', '□G→□⊥', '□(□G→□⊥)'], '□¬□⊥→□⊥', 'k4', { sys: 'K4', boss: true,
      intro: 'El jefe de la torre. La segunda premisa es lo que acabas de probar; la tercera, lo mismo dentro de una caja, porque T demuestra sus propios teoremas. Demuestra que si T demuestra su consistencia, {□¬□⊥}, entonces es inconsistente.',
      hints: ['Supón {□¬□⊥}. Con el teorema {(□G→□⊥)→(¬□⊥→¬□G)}, {Mon} sobre la premisa 3 y {RK} con el supuesto, obtienes {□¬□G}.', 'Con el teorema {(G↔¬□G)→(¬□G→G)}, {Mon} sobre la premisa 1 y {RK} con {□¬□G}, obtienes {□G}.', 'La premisa 2 y {MP} dan {□⊥}. Termina con {TD}.'],
      sol: [['H', '□¬□⊥'],
        ['H', '□G→□⊥'], ['H', '¬□⊥'], ['H', '□G'], ['MP', [5, 7]], ['¬E', [8, 6]], ['¬I'], ['TD'], ['TD'], ['Mon', [12, 3]], ['RK', [13, 4]],
        ['H', 'G↔¬□G'], ['H', '¬□G'], ['↔E', [15, 16], 'G'], ['TD'], ['TD'], ['Mon', [19, 1]], ['RK', [20, 14]], ['MP', [2, 21]], ['TD']] }),
    T('Después de Gödel', [
      { say: 'El argumento del segundo teorema tiene una forma general, el <b>teorema de Löb</b>: si T demuestra «si A es demostrable, entonces A», es que T ya demuestra {A}. En símbolos, {□(□A→A)→□A}. El segundo teorema es el caso en que {A} es {⊥}.' },
      { say: 'Añadir ese principio a K4 da la <b>lógica de la demostrabilidad</b>, GL: la lógica modal exacta de lo que una teoría como PA puede decir sobre sus propias pruebas.' },
      { say: 'En 1936 Alan Turing llegó a la incompletud por otro camino. Ningún programa decide, en general, si otro programa se detiene. Si una teoría fuera completa y correcta sobre esas cuestiones, bastaría buscar pruebas para decidirlo. Incompletud e <b>indecidibilidad</b> son dos caras del mismo fenómeno.' },
      { say: 'La consistencia de PA sí se puede demostrar, pero desde fuera. Gerhard Gentzen lo hizo en 1936 con inducción transfinita hasta el ordinal {ε₀}, un principio que PA no puede justificar. El programa de Hilbert no murió: cambió de forma.', mood: 'neutral' },
      { say: 'También hay oraciones indecidibles «naturales», sin autorreferencia: el teorema de Goodstein no se demuestra en PA, y la hipótesis del continuo no se decide en la teoría de conjuntos usual. La incompletud no es un truco: es un rasgo de la matemática.' }
    ]),
    Q('Examen de la torre', [
      { q: '¿Qué dice la oración de Gödel?', opts: ['«Soy falsa»', '«No soy demostrable en T»', '«T es inconsistente»'], ok: 1,
        why: 'Habla de demostrabilidad, no de verdad. Por eso no es paradójica.' },
      { q: 'En la prueba semántica se supone que T es…', opts: ['correcta: solo demuestra verdades', 'completa', 'decidible'], ok: 0,
        why: 'La prueba sintáctica cambia esa hipótesis por la consistencia, que no menciona la verdad.' },
      { q: 'Gödel usó una hipótesis extra para mostrar que T no demuestra {¬G}. ¿Cuál era y quién la eliminó?', opts: ['La {ω}-consistencia; Rosser', 'La completitud; Tarski', 'La inducción; Peano'], ok: 0,
        why: 'Con la oración de Rosser basta la consistencia simple.' },
      { q: 'Si T es consistente, ¿puede demostrar {Con(T)}?', opts: ['Sí, siempre', 'No: es el segundo teorema', 'Solo si T es PA'], ok: 1,
        why: 'Si la demostrara, demostraría {G}, y eso es imposible para una teoría consistente.' },
      { q: 'Si lees {□A} como «T demuestra A», ¿qué axioma modal <i>no</i> vale?', opts: ['{4}: {□A→□□A}', '{T}: {□A→A}', '{K}: {□(A→B)→(□A→□B)}'], ok: 1,
        why: 'Por el teorema de Löb, T solo demuestra {□A→A} cuando ya demuestra {A}. ¡Has llegado a lo más alto de la torre!' }
    ]),
    V('El oráculo de Löb', 'modal', { sys: ['K4', 'GL'], syms: '¬∧∨→↔⊥□', goals: ['split', 'valid', 'own'],
      intro: 'Lee {□A} como «la teoría demuestra A». K4 es lo que usaste en la torre. <b>GL</b> (Gödel-Löb) añade el axioma de Löb, {□(□A→A)→□A}, y por el teorema de Solovay es exactamente la lógica de la demostrabilidad en PA. Compara los dos sistemas.',
      outro: 'Los modelos de GL no tienen ciclos ni cadenas infinitas hacia adelante. Por eso en GL no vale {□A→A}: una teoría consistente no demuestra su propia corrección.',
      ex: [[[], '□(□P→P)→□P', 'invalid', 'K4'], [['¬□⊥'], '¬□¬□⊥', 'invalid', 'K4'], [['□(G↔¬□G)'], '□G→□⊥', 'valid', 'K4'], [['□(G↔¬□G)', '¬□⊥'], '¬□G', 'valid', 'K4'], [['□(G↔¬□G)', '¬□⊥'], '¬□¬G', 'invalid', 'GL'], [['□P'], 'P', 'invalid', 'GL']] })
  ]
};

root.CONTENT = { RS, GODEL, worlds: [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9] };
})(typeof window !== 'undefined' ? window : globalThis);
