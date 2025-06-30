#import "template/main.typ": *

#show: it => basic-report(
  doc-category: "Lenguajes Formales y Computabilidad | FAMAF - UNC",
  doc-title: "Combos de definiciones y convenciones notacionales y los Combos de teoremas",
  author: "Matias Viola",
  heading-font: "Computer Modern",
  heading-color: black,
  it,
)

// Definición de símbolos
#let Sast = $Sigma^ast$

= Convenciones

Si no se especifica lo contrario, usaremos las siguientes convenciones:
+ $x, y, z, u, v, w, n, m, k, ... in omega$
+ $alpha, beta, gamma, delta, epsilon, psi, eta, ... in Sast$
+ $O, s in {(omega, hash), (Sast, ast)}$
+ "tq" es "tal que"
+ $Sigma$-pr es "$Sigma$-primitivo recursivo"
+ Sea $f : "Dom"_f -> {0, 1}$, entonces $f$ es un predicado.

= Combos de definiciones y convenciones notacionales

== Combo 1: Defina:
=== Cuando un conjunto $S subset.eq omega^n times Sast^m$ es llamado $Sigma$-recursivo

Un conjunto $S subset.eq omega^n times Sast^m$ sera llamado $Sigma$-recursivo cuando la función $chi^(omega^n times Sast^m)_S$ sea $Sigma$-recursiva.

=== $angle.l s_1, s_2, ... angle.r$

Dada una infinitupla $(s_1, s_2, ...) ∈ omega^([NN])$ usaremos $angle.l s_1, s_2, ... angle.r$ para denotar al numero $product^oo_(i=1) "pr"(i)^(s_i)$

=== "$f$ es una función $Sigma$-mixta"

Sea $Sigma$ un alfabeto finito. Una función $f$ es $Sigma$-mixta si:
+ $(exists n, m in omega) "Dom"_f subset.eq omega^n times Sast^m$

+ $"Im"_f subset.eq O$

=== "familia $Sigma$-indexada de funciones"

Dado un alfabeto $Sigma$, una familia $Sigma$-indexada de funciones sera una función $rho.alt: Sigma -> "Im"_G$ donde $"Im"_G$ es el conjunto de funciones $rho.alt(a)$ asociadas a cada $a in Sigma$.

NOTACIÓN: Si $rho.alt$ es una familia $Sigma$-indexada de funciones, entonces para $a in Sigma$, escribiremos $rho.alt_a$ en lugar de $rho.alt(a)$.

=== $R(f, rho.alt)$: Recursion primitiva sobre variable alfabética con valores numéricos.
Sean $S_1, ..., S_n subset.eq omega$ y $L_1, ..., L_m subset.eq Sast$ conjuntos no vacíos.

Sea una función $f : S_1 times ... times S_n times L_1 times ... times L_m -> omega$.

Sea una familia $Sigma$-indexada de funciones $rho.alt_a : omega times S_1 times ... times S_n times L_1 times ... times L_m times Sast -> omega$ para cada $a in Sigma$.

$R(f, rho.alt) : S_1 times ... times S_n times L_1 times ... times L_m times Sast &-> omega\
(arrow(x), arrow(alpha), epsilon) &-> f(arrow(x), arrow(alpha))\
(arrow(x), arrow(alpha), alpha a) &-> rho.alt_a (R(f, rho.alt)(arrow(x), arrow(alpha), alpha), arrow(x), arrow(alpha), alpha)$

También diremos que $R(f, rho.alt)$ es obtenida por recursion primitiva a partir de $f$ y $rho.alt$.

== Combo 2: Defina:
=== $d tack.r^n d'$ y $d tack.r^ast d'$
(no hace falta que defina $tack.r$)

- $d tack.r^n d'$ si $(exists d_2, ..., d_n in "Des") d tack.r d_2 tack.r ... tack.r d_n tack.r d'$.

- $d tack.r^ast d'$ sii $(exists n in omega) d tack.r^n d'$
=== $L(M)$

Llamamos $L(M)$ al conjunto formado por todas las palabras que son aceptadas por alcance de estado final.

Una palabra $alpha_1...alpha_n in Sast$ es aceptada por $M$ por alcance de estado final si partiendo de $B q_0 alpha_1 ... alpha_n B...$ en algún momento de la computación $M$ esta en un estado de $F$.

=== "f es una función de tipo $(n, m, s)$"

Dada una función $Sigma$-mixta $f$,
- Si $f = emptyset$, entonces es una función de tipo $(n, m, s)$ cualquiera sean $n, m in omega$ y $s in { hash, ast }$.
- Si $f != emptyset$, entonces hay únicos $n, m in omega$ tales que $D_f subset.eq omega^n times Sast^m$.
  - Si $I_f subset.eq omega$, entonces es una función de tipo $(n, m, hash)$.
  - Si $I_f subset.eq Sast$, entonces es una función de tipo $(n, m, ast)$.

De esta forma, cuando $f != emptyset$, hablaremos de "el tipo de $f$" para referirnos a esta única terna $(n, m, s)$.

=== $(x)$

Dado $x in NN$, usaremos $(x)$ para denotar a la única infinitupla $(s_1, s_2, ...) in omega^[NN]$ tq $x = angle.l s_1, s_2, ... angle.r = product^oo_(i=1) "pr"(i)^(s_i)$

=== $(x)_i$

Dados $x, i in NN$, usaremos $(x)_i$ para denotar a $s_i$ de $(s_1, s_2, ...) = (x)$.

Se le suele llamar la "i-esima bajada de x" al numero $(x)_i$ (al "bajar" el i-esimo exponente de la única posible factorización de $x$ como producto de primos).

== Combo 3: Defina:
=== Cuando un conjunto $S subset.eq omega^n times Sast^m$ es llamado $Sigma$-recursivamente enumerable
(no hace falta que defina "función $Sigma$-recursiva")

Diremos que un conjunto $S subset.eq omega^n times Sast^m$ sera llamado $Sigma$-recursivamente enumerable cuando sea vacío o haya una función sobreyectiva $F : omega -> S$ tq $F_((i)) = p^(n,m)_i compose F$ sea $Sigma$-recursiva para cada $i in {1,...,n+m}$.

=== $s^<=$

Sea $<=$ un orden sobre $Sast$.

$S^<= : Sast &-> Sast \
(a_n)^m &-> (a_1)^(m+1) \
alpha a_i (a_n)^m &-> alpha a_(i+1) (a_1)^m$ con $1<=i<n$

=== $ast^<=$

Sea $<=$ un orden sobre $Sast$.

$ast^<= : omega &-> Sast\
0 &-> epsilon\
i+1 &-> s^<= (ast^<= (i))$

=== $hash^<=$

Sea $<=$ un orden sobre $Sast$.

$hash^<= : Sast &-> omega\
epsilon &-> 0\
a_i_k...a_i_0 &-> i_k n^k+...+i_0 n^0$

== Combo 4: Defina cuando una función $f : D_f subset.eq omega^n times Sast^m -> omega$ es llamada $Sigma$-efectivamente computable y defina "el procedimiento $P$ computa a la función $f$"

Sea $O$. Una función $Sigma$-mixta $f : "Dom"_f subset.eq omega^n times Sast^m -> O$ sera llamada $Sigma$-efectivamente computable si hay un procedimiento efectivo $P$ tq
+ El conjunto de datos de entrada de $P$ es $omega^n times Sast^m$
+ El conjunto de datos de salida esta contenido en $O$.
+ Si $(arrow(x), arrow(alpha)) in "Dom"_f$, entonces $P$ se detiene partiendo de $(arrow(x), arrow(alpha))$, dando como dato de salida $f(arrow(x), arrow(alpha)).$
+ Si $(arrow(x), arrow(alpha)) in omega^n times Sast^m - "Dom"_f$ , entonces $P$ no se detiene partiendo desde $(arrow(x), arrow(alpha))$

En ambos casos diremos que $P$ computa a la función $f$.

Obs: $f=emptyset$ es un procedimiento que nunca se detiene cualesquiera sea su dato de entrada. Por lo tanto es $Sigma$-efectivamente computable, cualesquiera sean $n, m, O$ y $Sigma$.

== Combo 5: Defina cuando un conjunto $S subset.eq omega^n times Sast^m$ es llamado $Sigma$-efectivamente computable y defina: "el procedimiento efectivo $P$ decide la pertenencia a $S$"

Un conjunto $S subset.eq omega^n times Sast^m$ sera llamado $Sigma$-efectivamente computable cuando la función $chi^(omega^n times Sast^m)_S$ sea $Sigma$-efectivamente computable.

Si $P$ es un procedimiento efectivo el cual computa a $chi^(omega^n times Sast^m)_S$, entonces diremos que $P$ decide la pertenencia a $S$, con res_pecto al conjunto $omega^n times Sast^m$.

Obs: $f=emptyset$ es un procedimiento que siempre da 0 cualesquiera sea su dato de entrada. Por lo tanto es $Sigma$-efectivamente computable, cualesquiera sean $n, m, O$ y $Sigma$.

== Combo 6: Defina cuando un conjunto $S subset.eq omega^n times Sast^m$ es llamado $Sigma$-efectivamente enumerable y defina: "el procedimiento efectivo $P$ enumera a $S$"

Un conjunto $S subset.eq omega^n times Sast^m$ sera llamado $Sigma$-efectivamente enumerable cuando sea vacío o haya una función sobreyectiva $F : omega -> S$ tq $F_((i))$ sea $Sigma$-efectivamente computable, para cada $i in {1, ..., n + m}$.

== Combo 7: Defina cuando una función $f : D_f subset.eq omega^n times Sast^m -> omega$ es llamada $Sigma$-Turing computable y defina "la máquina de Turing $M$ computa a la función $f$"

Diremos que una función $f : "Dom"_f subset.eq omega^n times Sast^m -> Sast$ es $Sigma$-Turing computable si existe una máquina de Turing con unit, $M = (Q, Sast, Γ, δ, q_0, B, nu, F)$ tq:
+ Si $(arrow(x), arrow(alpha)) in "Dom"_f$, entonces hay un $p in Q$ tq $floor.l q_0 B nu^(x_1) B...B nu^(x_n) B alpha_1 B ... B alpha_m floor.r tack.r^ast floor.l p B f(arrow(x), arrow(alpha)) floor.r$ y $floor.l p B f(arrow(x), arrow(alpha)) floor.r tack.r.not d$ para cada $d in "Des"$
+ Si $(arrow(x), arrow(alpha)) in omega^n times Sast^m - "Dom"_f$, entonces $M$ no se detiene partiendo de $floor.l q_0 B nu^(x_1) B...B nu^(x_n) B alpha_1 B ... B alpha_m floor.r$.

Cuando una maquina de Turing con unit $M$ cumpla ambos items, diremos que $M$ computa a la función $f$ o que $f$ es computada por $M$.

Cabe destacar que la condición $floor.l p B f(arrow(x), arrow(alpha)) floor.r tack.r.not d$ para cada $d in "Des"$ es equivalente a que $(p, B)$ no este en el dominio de $delta$ o que si lo este y que la tercer
coordenada de $delta (p, B)$ sea $L$.

== Combo 8: Defina:
=== $M(P)$ Minimización de variable numérica
Sea $Sigma$ un alfabeto finito y sea $P : "Dom"_P subset.eq omega^n times Sast^m$. Dado $(arrow(x), arrow(alpha)) in omega^n times Sast^m$, cuando exista al menos un $t in omega$ tq $P(t, arrow(x), arrow(alpha)) = 1$, usaremos $min_t P(t, arrow(x), arrow(alpha))$ para denotar al menor de tales $t$'s.

Definimos $M(P) = lambda arrow(x) arrow(alpha) [min_t P(t, arrow(x), arrow(alpha))]$

Diremos que $M(P)$ es obtenida por minimización de variable numérica a partir de $P$.

Obs: $M(P)$ esta definida solo para aquellas $(n + m)$-uplas $(arrow(x), arrow(alpha))$ para las cuales hay al menos un $t$ tq se da $P(t, arrow(x), arrow(alpha)) = 1$

=== $"Lt"$

$"Lt" : NN &-> omega\
1 &-> 0\
x &-> max_i (x)_i != 0$

=== Conjunto rectangular

#let def_conjunto_rectangular = [Sea $Sigma$ un alfabeto finito. Un conjunto $Sigma$-mixto es llamado rectangular si es de la forma $S_1 times ... times S_n times L_1 times ... times L_m$ con cada $S_i subset.eq omega$ y cada $L_i subset.eq Sast$.]

#def_conjunto_rectangular

=== "$S$ es un conjunto de tipo $(n, m)$"

Dado un conjunto $Sigma$-mixto $S != emptyset$, decimos que $S$ es un conjunto de tipo $(n, m)$ para referirnos a los únicos $n, m in omega$ tq $S subset.eq omega^n times Sast^m$

$emptyset$ es un conjunto de tipo $(n, m)$ cualesquiera sean $n, m in omega$ por lo cual cuando hablemos de el tipo de un conjunto deberemos estar seguros de que dicho conjunto es no vacío.

== Combo 9
=== Conjunto rectangular

#def_conjunto_rectangular

=== "$I$ es una instrucción de $S^Sigma$"

Una instrucción de $S^Sigma$ es ya sea una instrucción básica de $S^Sigma$ o una palabra de la forma $alpha I$, donde $alpha in {L overline(n) : n in NN}$ y $I$ es una instrucción básica de
$S^Sigma$. Llamamos $"Ins"^Sigma$ al conjunto de todas las instrucciones de $S^Sigma$.

=== "$P$ es un programa de $S^Sigma$"

Un programa de $S^Sigma$ es una palabra de la forma $I_1 I_2...I_n$ donde $n >= 1, I_1, ..., I_n in "Ins"^Sigma$ y se cumple la ley de los GOTO.

Ley de los GOTO: Para cada $i in {1, ..., n}$, si GOTO $L overline(m)$ es un tramo final de $I_i$, entonces existe $j in {1, ..., n}$ tq $I_j$ tiene label $L overline(m)$.

=== $I^P_i$

$lambda i P[I^P_i] : omega times "Pro"^Sigma &-> Sast\
(i, P) &-> cases("i-esima instrucción de P" &"si" i in {1, ..., n(P)}, epsilon &"si" i in.not {1, ..., n(P)})$

=== $n(P)$

$lambda P [n(P)] : "Pro"^Sigma &-> omega\
P &-> m "tq" P = I_1 I_2...I_m$

=== $"Bas"$

$"Bas" : "Ins"^Sigma &-> (Sigma union Sigma_p)^ast\
I &-> cases(J &"si" I "es de la forma" L overline(k) J "con" J in "Ins"^Sigma, I &"c.c.")$

== Combo 10: Defina relativo al lenguaje $S^Sigma$:
=== "estado"

Es un par $(arrow(x), arrow(sigma)) = ((s_1, s_2, ...),(sigma_1, sigma_2, ...)) in omega^[NN] times Sast^[NN]$

Si $i >= 1$, entonces diremos que $s_i$ es el valor de la variable $N overline(i)$ y $alpha_i$ es el valor de la variable $P overline(i)$ en el estado $(arrow(x), arrow(sigma))$.

=== "descripción instantánea"

Es una terna $(i, arrow(x), arrow(sigma)) in "Des"^Sigma = omega times omega^[NN] times Sast^[NN]$ tq $(arrow(x), arrow(sigma))$ es un estado.

Si $i in {1, ..., n(P)}$, $(i, arrow(x), arrow(sigma))$ nos dice que las variables están en el estado $(arrow(x), arrow(sigma))$ y que la instrucción que debemos realizar es $I_i^P$

=== $S_P$

Dado un programa $P$.

$S_P : "Des"^Sigma &-> "Des"^Sigma\
(i, arrow(x), arrow(sigma)) &-> cases(
  (i, arrow(x), arrow(sigma)) &"si" i in.not {1, ..., n(P)}, (i + 1, (s_1, ..., s_k - 1, ...), arrow(sigma)) &"si" "Bas"(I^P_i) = N overline(k) <- N overline(k) - 1,
  (i + 1, (s_1, ..., s_k + 1, ...), arrow(sigma)) &"si" "Bas"(I^P_i) = N overline(k) <- N overline(k) + 1,
  (i + 1, (s_1, ..., s_n, ...), arrow(sigma)) &"si" "Bas"(I^P_i) = N overline(k) <- N overline(n),
  (i + 1, (s_1, ..., 0, ...), arrow(sigma)) &"si" "Bas"(I^P_i) = N overline(k) <- 0,
  (i + 1, arrow(s), arrow(sigma)) &"si" "Bas"(I^P_i) = "IF" N overline(k) != 0 "GOTO" L overline(m) and s_k = 0,
  (min { l : I^P_l "tiene label" L overline(m) }, arrow(s), arrow(sigma)) &"si" "Bas"(I^P_i) = "IF" N overline(k) != 0 "GOTO" L overline(m) and s_k != 0,
  (i + 1, arrow(s), (sigma_1, ..., arrow.cw.half sigma_k, ...)) &"si" "Bas"(I^P_i) = P overline(k) <- arrow.cw.half P overline(k),
  (i + 1, arrow(s), (sigma_1, ..., sigma_k a, ...)) &"si" "Bas"(I^P_i) = P overline(k) <- P overline(k) . a,
  (i + 1, arrow(s), (sigma_1, ..., sigma_macron(n), ...)) &"si" "Bas"(I^P_i) = P overline(k) <- P overline(n),
  (i + 1, arrow(s), (sigma_1, ..., epsilon , ...)) &"si" "Bas"(I^P_i) = P overline(k) <- epsilon,
  (min { l : I^P_l "tiene label" L overline(m) }, arrow(s), arrow(sigma)) &"si" "Bas"(I^P_i) = "IF" P overline(k) "BEGINS" a "GOTO" L overline(m) and [sigma_k]_1 = a,
  (i + 1, arrow(s), arrow(sigma)) &"si" "Bas"(I^P_i) = "IF" P overline(k) "BEGINS" a "GOTO" L overline(m) and [sigma_k]_1 != a,
  (min { l : I^P_l "tiene label" L overline(m) }, arrow(s), arrow(sigma)) &"si" "Bas"(I^P_i) = "GOTO" L overline(m),
  (i + 1, arrow(s), arrow(sigma)) &"si" "Bas"(I^P_i) = "SKIP"
)$


=== "estado obtenido luego de $t$ pasos, partiendo del estado $(arrow(x), arrow(alpha))$"

Dado un programa $P$ y la descripción instantánea obtenida luego de $t$ pasos desde el estado $(arrow(x), arrow(sigma))$
$ overbrace(S_P \(...S_P \(S_P, "t veces") (1, arrow(x), arrow(sigma)))...) = (j, arrow(u), arrow(eta)) $
diremos que $(arrow(u), arrow(eta))$ es el estado obtenido luego de t pasos, partiendo del estado $(arrow(x), arrow(sigma))$.

=== "$P$ se detiene (luego de $t$ pasos), partiendo desde el estado $(arrow(x), arrow(alpha))$"

Dado $overbrace(S_P \(...S_P \(S_P, "t veces") (1, arrow(x), arrow(sigma)))...) = (j, arrow(u), arrow(eta))$, si su primer coordenada $j$ es igual a $n(P)+1$, diremos que $P$ se detiene (luego de $t$ pasos), partiendo desde el estado $(arrow(x), arrow(sigma))$.

== Combo 11: Defina:
=== $Psi^("n,m,#")_P$

Dado $P in "Pro"^Sigma$.

$D_(Psi_P^(n, m, hash)) = {(arrow(x), arrow(sigma)) in omega^n times Sast^m : P "termina partiendo de" ||x_1, ..., x_n, alpha_1, ..., alpha_m||}$

$Psi_P^(n, m, hash) : D_(Psi_P^(n, m, hash)) &-> omega\
(arrow(x), arrow(sigma)) &-> "valor de" N_1 "cuando" P "termina partiendo de" ||x_1, ..., x_n, alpha_1, ..., alpha_m||$


=== "f es $Sigma$-computable" y "$P$ computa a $f$"

Dado $s, O in {(hash,omega), (ast, Sast)}$.
Una función $Sigma$-mixta $f : S subset.eq omega^n times Sast^m -> O$ sera llamada $Sigma$-computable si hay un programa $P$ de $S^Sigma$ tq $f = Psi_P^(n, m, s)$.

En tal caso diremos que la función $f$ es computada por $P$.

=== $M^<= (P)$ Minimización de variable alfabética

Sea que $Sigma != emptyset$. Sea $<=$ un orden
total sobre $Sigma$, $<=$ puede ser naturalmente extendido a un orden total sobre $Sast$. Sea $P : "Dom"_P subset.eq omega^n times Sast^m times Sast$ un predicado. Cuando $(arrow(x), arrow(alpha)) in omega^n times Sast^m$ es tq existe al menos un $alpha in Sast$ tq $P(arrow(x), arrow(alpha), alpha) = 1$, usaremos $min^<=_alpha P(arrow(x), arrow(alpha), alpha)$ para denotar al menor $alpha in Sast$ tq $P(arrow(x), arrow(alpha), alpha) = 1$.

Definimos $M^<= (P) = lambda arrow(x) arrow(alpha) [min^<=_alpha P(arrow(x), arrow(alpha), alpha)]$

Diremos que $M^<= (P)$ es obtenida por minimización de variable alfabética a partir de $P$.

Obs: $M^<= (P)$ esta definida solo para aquellas $(n + m)$-uplas $(arrow(x), arrow(alpha))$ para las cuales hay al menos un $alpha$ tq se da $P(arrow(x), arrow(alpha), alpha) = 1$


== Combo 12: Defina cuando un conjunto $S subset.eq omega^n times Sast^m$ es llamado $Sigma$-computable, cuando es llamado $Sigma$-enumerable y defina "el programa $P$ enumera a $S$"

Un conjunto $S subset.eq omega^n times Sast^m$ sera llamado $Sigma$-computable cuando la función $chi^(omega^n times Sast^m)_S$ sea $Sigma$-computable.

Un conjunto $S subset.eq omega^n times Sast^m$ sera llamado $Sigma$-enumerable cuando sea vacío o haya
una función sobreyectiva $F : omega -> S$ tq $F_((i))$ sea $Sigma$-computable, para cada $i in {1, ..., n + m}$.

Nótese que, un conjunto no vacío $S subset.eq omega^n times Sast^m$ es $Sigma$-enumerable sii hay programas $P_1, ..., P_(n+m)$ con dato de entrada $x in omega$ tales que:

$ S = "Im"[Psi^(1,0,hash)_(P_1), ..., Psi^(1,0,hash)_(P_n), Psi^(1,0,ast)_(P_(n+1)), ..., Psi^(1,0,ast)_(P_(n+m))] $

Como puede notarse, los programas $P_1, ..., P_(n+m)$ puestos secuencialmente a funcionar desde el estado $||x||$ producen, en forma natural, un procedimiento efectivo que enumera a $S$. Es decir que los programas $P_1, ..., P_(n+m)$ enumeran a $S$.


== Combo 13
Defina:
=== $i^(n,m)$
$i^(n,m) : omega times omega^n times Sast^m times "Pro"^Sigma &-> omega\
(0, arrow(x), arrow(alpha), P) &-> 1\
(t, arrow(x), arrow(alpha), P) &-> j "tq" overbrace(S_P \(...S_P \(S_P, "t veces") (1, arrow(x), arrow(sigma)))...) = (j, arrow(u), arrow(eta))$

=== $E^(n,m)_hash$

$E^(n,m)_hash : omega times omega^n times Sast^m times "Pro"^Sigma &-> omega^[NN]\
(0, arrow(x), arrow(alpha), P) &-> (x_1, ..., x_n, 0, ...)\
(t, arrow(x), arrow(alpha), P) &-> arrow(u) "tq" overbrace(S_P \(...S_P \(S_P, "t veces") (1, arrow(x), arrow(sigma)))...) = (j, arrow(u), arrow(eta))$

=== $E^(n,m)_hash$ + $E^(n,m)_ast$

$E^(n,m)_ast : omega times omega^n times Sast^m times "Pro"^Sigma &-> Sast^[NN]\
(0, arrow(x), arrow(alpha), P) &-> (alpha_1, ..., alpha_n, epsilon, ...)\
(t, arrow(x), arrow(alpha), P) &-> arrow(eta) "tq" overbrace(S_P \(...S_P \(S_P, "t veces") (1, arrow(x), arrow(sigma)))...) = (j, arrow(u), arrow(eta))$

=== $E^(n,m)_(hash_j)$

$E^(n,m)_(hash_j) : omega times omega^n times Sast^m times "Pro"^Sigma -> omega$

$E^(n,m)_(hash_j) = p^(n,m)_j compose E^(n,m)_hash$

=== $E^(n,m)_(ast_j)$

$E^(n,m)_(ast_j) : omega times omega^n times Sast^m times "Pro"^Sigma -> Sast$

$E^(n,m)_(ast_j) = p^(n,m)_j compose E^(n,m)_ast$

=== $"Halt"^(n,m)$

$"Halt"^(n,m) : omega times omega^n times Sast^m times "Pro"^Sigma &-> {0, 1}\
(t, arrow(x), arrow(sigma), P) &-> i^(n,m) (t, arrow(x), arrow(alpha),P) = n(P) + 1$

=== $T^(n,m)$

$"Dom"_(T^(n,m)) = {(arrow(x), arrow(sigma), P) : P "se detiene partiendo de" ∥x_1, ..., x_n, alpha_1, ..., alpha_m∥}$

$T^(n,m) : "Dom"_(T^(n,m)) &-> omega\
(t, arrow(x), arrow(sigma), P) &-> min_t ("Halt"^(n,m) (t, arrow(x), arrow(sigma), P))$

=== $"AutoHalt"^Sigma$

Dado $Sigma supset.eq Sigma_p$

$"AutoHalt"^Sigma : "Pro"^Sigma &-> {0, 1}\
P &-> (exists t in omega) "Halt"^(0,1) (t, P, P)$

=== Los conjuntos $A$ y $N$

Dado $Sigma supset.eq Sigma_p$

$A = {P in "Pro"^Sigma : "AutoHalt"^Sigma (P)}$

$N = {P in "Pro"^Sigma : not "AutoHalt"^Sigma (P)}$

== Combo 14: Explique en forma detallada la notación lambda

Usamos la notación lambda de Church de la forma descrita a continuación.

Esta notación se define en función de un alfabeto finito previamente fijado, que denotaremos por $Sigma$.

Solo se usan expresiones tq:
+ *Variables permitidas*:
  - Se usan *variables numéricas* que se valúan en números de ($omega$), y se denotan por letras como $x, y, z, u, v, w, n, m, k, ...$.
  - Se usan *variables alfabéticas* que se valúan en palabras sobre el alfabeto $Sigma$. Se denotan por letras como $alpha, beta, gamma, delta, epsilon, psi, eta, ...$.

+ *Dominio parcial*: Las expresiones lambda pueden ser *parcialmente definidas*. Es decir, puede haber valuaciones de sus variables para las cuales la expresión no este definida.

+ *Libertad sintáctica*: Las expresiones pueden ser descritas informalmente.

+ *Valores booleanos*: Consideramos que las expresiones booleanas toman valores en el conjunto ${0, 1} ⊆ omega$ (usando $0$ para falso y $1$ para verdadero).

Dado un alfabeto $Sigma$ a las expresiones que cumplan las características dadas anteriormente las llamaremos lambdificables con respecto a $Sigma$.

== Combo 15: Dada una función $f : "Dom"_f subset.eq omega times Sast -> omega$, describa qué tipo de objeto es y qué propiedades debe tener el macro: [V2 ← f(V1,W1)]

Dada una función $f : "Dom"_f subset.eq omega times Sast -> omega$ $Sigma$-computable, la palabra
$ V overline(2) <- f(V 1, W 1) $
denota a un macro $M$ que cumple lo siguiente:

+ Sus variables oficiales son: $V 1, V 2, W 1$
+ No tiene labels oficiales.
+ Si reemplazamos (tanto oficiales como auxiliares en cada caso):
  + Las variables $V overline(k')$ por variables concretas $N overline(k)$ con $k$ distintos entre si.
  + Las variables $W overline(j')$ por variables concretas $P overline(j)$ con $j$ distintos entre si.
  + Los labels $A overline(z')$ por labels concretos $L overline(z)$ con $z$ distintos entre si.
  Obtenemos la palabra $N overline(k_2) <- f(N overline(k_1), P overline(j_1))$ la cual es un programa de $S^Sigma$.

  El cual debe cumplir que: Si lo hacemos correr partiendo de un estado $e$ que le asigne a las variables $N overline(k_1), N overline(k_2), P overline(j_1)$ valores $x_1, x_2, alpha_1$, se dará que
  + Si $(x_1, alpha_1) in.not "Dom"_P$, el programa no se detiene.
  + Si $(x_1, alpha_1) in "Dom"_P$, luego de una cantidad finita de pasos el programa se detiene llegando a un estado $e'$ tq:
    + $e'$ asigna a $N overline(k_2)$ el valor $f(x_1, alpha_1)$;
    + $e'$ solo difiere de $e$ en el valor de $N overline(k_2)$ y en las variables que reemplazaron a las auxiliares de $M$.

La palabra $N overline(k_2) <- f(N overline(k_1), P overline(j_1))$ se denomina la expansión del macro $V 2 <- f(V 1, W 1)$ respecto de la elección concreta de variables y labels realizada.

== Combo 16: Dado un predicado $p : D_f subset.eq omega times Sast -> omega$, describa qué tipo de objeto es y qué propiedades debe tener el macro: [IF P(V1,W1) GOTO A1]

Dado un predicado $P : "Dom"_P subset.eq omega times Sast -> {0, 1}$ $Sigma$-computable, la palabra
$ ["IF" P(V 1, W 1) "GOTO" A 1] $
denota a un macro $M$ que cumple lo siguiente:

+ Sus variables oficiales son: $V 1, W 1$
+ $A 1$ es su único label oficial.
+ Si reemplazamos (tanto oficiales como auxiliares en cada caso):
  + Las variables $V overline(k')$ por variables concretas $N overline(k)$ con $k$ distintos entre si.
  + Las variables $W overline(j')$ por variables concretas $P overline(j)$ con $j$ distintos entre si.
  + Los labels $A overline(z')$ por labels concretos $L overline(z)$ con $z$ distintos entre si.
  Obtenemos la palabra $["IF" P(N overline(k_1), P overline(j_1)) "GOTO" L overline(z_1)]$ la cual, si se cumple la ley del GOTO respecto a $L overline(z_1)$, es un programa de $S^Sigma$.

  El cual debe cumplir que: Si lo hacemos correr partiendo de un estado $e$ que le asigne a las variables $N overline(k_1), P overline(j_1)$ valores $x_1, alpha_1$, se dará que
  + Si $(x_1, alpha_1) in.not "Dom"_P$, el programa no se detiene.
  + Si $(x_1, alpha_1) in "Dom"_P$, luego de una cantidad finita de pasos:
    + Si $P(x_1, alpha_1) = 1$, se salta al label $L overline(z_1)$.
    + Si $P(x_1, alpha_1) = 0$, el programa se detiene.

    En ambos casos, el estado alcanzado $e'$ solo puede diferir de $e$ en las variables que reemplazaron a las auxiliares de $M$.

La palabra $["IF" P(N overline(k_1), P overline(j_1)) "GOTO" L overline(z_1)]$ se denomina la expansión del macro $["IF" P(V 1, W 1) "GOTO" A 1]$ respecto de la elección concreta de variables y labels realizada.


== Combo 17: Defina el concepto de función y desarrolle las tres Convenciones Notacionales asociadas a dicho concepto

Una función es un conjunto de pares tq, si $(x, y) in f$ y $(x, z) in f$, entonces $y = z$.

Dada una función $f$, definimos:
- $"Dom"_f = {x : (x, y) in f "para algún" y}$
- $"Im"_f = {y : (x, y) in f "para algún" x}$

Las convenciones notacionales son:
- Dado $x in "Dom"_f$, usaremos $f (x)$ para denotar al único $y in "Im"_f$ tq $(x, y) in f$.
- Escribimos $f : S subset.eq A -> B$ para expresar que $f$ es una función tq $"Dom"_f = S subset.eq A$ y $"Im"_f subset.eq B$. También escribimos $f : A -> B$ si $S = A$. En tal contexto llamaremos a $B$ conjunto de llegada.
- Muchas veces para definir una función $f$, lo haremos dando su dominio y su regla de asignación. Esto determina por completo a $f$ ya que $f = {(x, f(x)) : x in "Dom"_f }$.
  #grid(
    columns: 3,
    gutter: 1.5em,
    align: (left, center, right),

    [Básico], [Con conjunto de llegada y flechas], [Con flechas y por casos],

    [$"Dom"_f = omega \
      f(x) = 23 x$],

    [$f : omega &-> omega \
      x &-> 23 x$],

    [$f : NN &-> omega \
      x &->
      cases(
        x + 1 &"si x es par",
        x + 2 &"si x es impar"
      )$],
  )

= Combos de teoremas

== Combo 1
=== Proposición: Caracterización de conjuntos $Sigma$-pr
#let Proposición19 = [Sea $S subset.eq omega^n times Sast^m$.
  Entonces, $S$ es $Sigma$-pr sii $S$ es el dominio de alguna función $Sigma$-pr.]
#Proposición19 (En la inducción de la prueba hacer solo el caso de la composición)

*Prueba $=>$*

Sea $S$ $Sigma$-pr.\
Entonces, $chi^(omega^n times Sast^m)_S$ es $Sigma$-pr para algún $n, m in omega$.\
Para ese caso, $"pred" compose chi^(omega^n times Sast^m)_S$ es una función $Sigma$-pr y $S = "Dom"_("pred" compose chi^(omega^n times Sast^m)_S)$

*Prueba $arrow.l.double$*

Sea S el dominio de una función $Sigma$-pr $f : "Dom"_f subset.eq omega^n times Sast^m -> O$.\
Probaremos por inducción en $k$ que $"Dom"_F$ es $Sigma$-pr, para cada $F in "PR"^Sigma_k$:

+ Caso $k = 0$:
  $"PR"^Sigma_0 = {"suc", "pred", C^(0,0)_0, C^(0,0)_epsilon} union {d_a : a in Sigma} union {p^(n,m)_j : 1 <= j <= n + m}$
  Los dominios de las funciones $"suc", C^(0,0)_0, C^(0,0)_epsilon, d_a, p^(n,m)_j$ son de la forma $omega^n times Sast^m$ y $omega$ y $Sast$ son $Sigma$-pr, por el "Lema 16" son $Sigma$-pr.\
  Finalmente, $chi^omega_"Dom"_"Pred" = lambda x [x!=0]$ es $Sigma$-pr, por definición $"Dom"_"Pred"$ es $Sigma$-pr

+ Supongamos que $"Dom"_F$ es $Sigma$-pr $forall F in "PR"^Sigma_(k)$.

+ Sea $F in "PR"^Sigma_(k + 1)$. Veremos entonces que $"Dom"_F$ es $Sigma$-pr solo para el caso de composición:\
  Si $F = emptyset$, entonces es claro que $"Dom"_F = emptyset$ es $Sigma$-pr.\
  Sea $F = g compose [g_1, ..., g_(n+m)]$ no vacío, con $g, g_1, ..., g_(n+m) in "PR"^Sigma_k$.
  - $g : "Dom"_g subset.eq omega^n times Sast^m -> O$
  - $g_i : "Dom"_g_i subset.eq omega^k times Sast^l -> omega$ para $i = 1, ..., n$
  - $g_i : "Dom"_g_i subset.eq omega^k times Sast^l -> Sast$ para $i = n+1, ..., n+m$

  Por hipótesis inductiva, los conjuntos $"Dom"_g, "Dom"_g_i$ son $Sigma$-pr.\
  Por "Lema 15", $S = inter.big_(i=1)^(n + m) "Dom"_g_i$ es $Sigma$-pr.\

  Por "Lema 20" y "Lema 18", $chi^(omega^k times Sast^l)_("Dom"_F)(arrow(x), arrow(alpha)) = cases(chi^(omega^n times Sast^m)_("Dom"_g) compose [g_1, ..., g_(n+m)] &"si" (arrow(x), arrow(alpha)) in S, C^(k,l)_0 &"si" (arrow(x), arrow(alpha)) in omega^k times Sast^l - S)$ es $Sigma$-pr.

  Por lo tanto $"Dom"_F$ es $Sigma$-pr


=== Teorema: Neumann vence a Gödel
Si $h$ es $Sigma$-recursiva, entonces $h$ es $Sigma$-computable. (En la inducción de la prueba hacer solo el caso $h = R(f, rho.alt)$, con $I_h subset.eq omega$)

*Prueba:*

Probaremos por inducción en $k$ que:  Si $h in R^Sigma_k$, entonces $h$ es $Sigma$-computable:

+ Caso k=0: $"R"^Sigma_0 = "PR"^Sigma_0 = {"suc", "pred", C^(0,0)_0, C^(0,0)_epsilon} union {d_a : a in Sigma} union {p^(n,m)_j : 1 <= j <= n + m}$ Por lo que dados los programas que los computan (dejado al lector), entonces son $Sigma$-computables.

+ Supongamos que $h in R^Sigma_k => h$ es $Sigma$-computable.

+ Veamos que $h in R^Sigma_(k+1) - R_k => h$ es $Sigma$-computable  para el caso $h = R(f, rho.alt)$ con $"Im"_h subset.eq omega$.\
  Sean
  - $Sigma = {a_1, ..., a_r}$
  - $(f in R^Sigma_k) f: S_1 times ... times S_n times L_1 times ... times L_m -> omega$
  - $(forall a in Sigma, rho.alt_a in R^Sigma_k) rho.alt_a : omega times S_1 times ... times S_n times L_1 times ... times L_m times Sast -> omega$

  Por hipótesis inductiva, $f$ y cada $rho.alt_a$ son $Sigma$-computables por lo que existen sus macros.\
  Recordemos:

  $
    R(f, rho.alt) : S_1 times ... times S_n times L_1 times ... times L_m times Sast &-> omega\
    (arrow(x), arrow(alpha), epsilon) &-> f(arrow(x), arrow(alpha))\
    (arrow(x), arrow(alpha), alpha a) &-> rho.alt_a (R(f, rho.alt)(arrow(x), arrow(alpha), alpha), arrow(x), arrow(alpha), alpha)
  $

  Entonces, construimos el siguiente programa usando macros:

  $
    &N overline(n+1) <- f(N 1, ..., N overline(n), P 1, ..., P overline(m))\
    L overline(r+1): &"IF" P overline(m+1) "BEGINS" a_1 "GOTO" L 1\
    &dots.v\
    &"IF" P overline(m+1) "BEGINS" a_r "GOTO" L r\
    &"GOTO" L overline(r+2)\
    L 1: &P overline(m+1) <- arrow.cw.half P overline(m+1)\
    &N overline(n+1) <- rho.alt_(a_1)(N overline(n+1), N 1, ..., N overline(n), P 1, ..., P overline(m), P overline(m+2))\
    &P overline(m+2) <- P overline(m+2).a_1\
    &"GOTO" L overline(r+1)\
    &dots.v\
    L r: &P overline(m+1) <- arrow.cw.half P overline(m+1)\
    &N overline(n+1) <- rho.alt_(a_r)(N overline(n+1), N 1, ..., N overline(n), P 1, ..., P overline(m), P overline(m+2))\
    &P overline(m+2) <- P overline(m+2).a_r\
    &"GOTO" L overline(r+1)\
    L overline(r+2): &N 1 <- N overline(n+1)
  $

  Este programa computa h.

== Combo 2
=== Lema 20: Lema de división por casos para funciones $Sigma$-pr
#let Lema20 = [Si $f_i : "Dom"_f_i subset.eq omega^n times Sast^m -> O$ para $i=1,...,k$ son $Sigma$-pr tq si $i != j => "Dom"_f_i inter "Dom"_f_j = emptyset$, entonces la función $f = union.big_(i=1)^k f_i$ es también $Sigma$-pr.]

#Lema20 (Hacer el caso $O = Sast$, $k = 2$, $n = 2$ y $m = 1$)

*Prueba:*

Supongamos $O = Sast$, $i = 1, 2$, $n = 2$ y $m = 1$.\
Sean $f_i : "Dom"_f_i subset.eq omega^2 times Sast^2 -> Sast$ $Sigma$-pr tq si $i != j => "Dom"_f_i inter "Dom"_f_j = emptyset$.

Por "Lema 18", existen funciones $Sigma$-totales $Sigma$-pr $overline(f)_i : omega^2 times Sast^2 -> Sast$ tq $f_i = overline(f)_i|_"Dom"_(f_i)$.\
Por "Proposición 19", los conjuntos $"Dom"_(f_1)$ y $"Dom"_(f_2)$ son $Sigma$-pr.\
Por lo tanto, por "Lema 15", también lo es su unión: $"Dom"_(f_1) union "Dom"_(f_2)$.\
Finalmente, por "Lema 17",
$
  f_1 union f_2 =
  ( lambda alpha beta [alpha beta] compose
    [ lambda x alpha [alpha^x] compose
      [ chi^(omega^n times Sast^m)_"Dom"_(f_1), overline(f)_1 ]
      union lambda x alpha [alpha^x] compose
      [ chi^(omega^n times Sast^m)_"Dom"_(f_2), overline(f)_2 ]
    ]
  )|_("Dom"_(f_1) union "Dom"_(f_2))
$
es $Sigma$-pr.

#let ProposiciónCaracterizaciónbásicadeconjuntosSigmaenumerables = [
  === Proposición: Caracterización básica de conjuntos $Sigma$-enumerables
  Sea $S subset.eq omega^n times Sast^m$ un conjunto no vacío. Entonces son equivalentes:
  + $S$ es $Sigma$-enumerable
  + Hay un programa $PP in "Pro"^Sigma$ tq:
    + Para cada $x in omega$, $PP$ se detiene partiendo desde el estado $||x||$ y llega a un estado de la forma $((x_1, ..., x_n, y_1, ...), (alpha_1, ..., alpha_m, beta_1, ...))$, donde $(x_1, ..., x_n, alpha_1, ..., alpha_m) in S$
    + Para cada $(x_1, ..., x_n, alpha_1, ..., alpha_m) in S$ hay un $x in omega$ tq $PP$ se detiene partiendo desde el estado $||x||$ y llega a un estado como en $((x_1, ..., x_n, y_1, ...), (alpha_1, ..., alpha_m, beta_1, ...))$
  (Hacer el caso $n = 2$ y $m = 1$)


  Sea $n = 2$, $m = 1$ e $i = 1, 2, 3$.

  *Prueba $=>$:*

  Hipótesis: Dado $S subset.eq omega^2 times Sast^1$ no vacío y $Sigma$-enumerable.

  Por definición existe una función sobreyectiva $F : omega -> S$ tq $F_((i))$ son $Sigma$-computable.\
  Por "Proposición 4.8", existen macros para $F_((1))$, $F_((2))$ y $F_((3))$.\
  Sea $QQ$ el siguiente programa:

  $
    & P 1 <- F_((3))(N 1) \
    & N 2 <- F_((2))(N 1) \
    & N 1 <- F_((1))(N 1)
  $

  donde:
  - Ninguna expansion usa las variables auxiliares $N 1, N 2, P 1$
  - Dos expansiones distintas no usan el mismo label auxiliar.

  Sea $PP$ el siguiente programa que extiende $QQ$:

  $
    & QQ             \
    & P 2 <- epsilon \
  $

  $PP$ cumple las condiciones ya que emula el comportamiento de $F$ quien enumera a $S$.

  *Prueba $arrow.l.double$:*

  Hipótesis: Dado $PP in "Pro"^Sigma$ tq cumple las condiciones (a) y (b).

  Sean:
  - $PP_1 &= PP N 1 <- N 1$
  - $PP_2 &= PP N 1 <- N 2$
  - $PP_3 &= PP P 1 <- P 1$


  Tenemos:
  - $F_((1)) &= Psi^(1, 0, hash)_(PP_1)$
  - $F_((2)) &= Psi^(1, 0, hash)_(PP_2)$
  - $F_((3)) &= Psi^(1, 0, ast)_(PP_3)$

  Por definición, cada $F_((i))$ es $Sigma$-computable.\
  Por lo tanto $F = [F_((1)), F_((2)), F_((3))]$ es $Sigma$-computable.\
  Por hipótesis, dado que $F$ emula a $PP$, $"Dom"_F = omega$ y $"Im"_F = S$.\
  Por lo tanto $S$ es $Sigma$-enumerable.
]
#ProposiciónCaracterizaciónbásicadeconjuntosSigmaenumerables
== Combo 3
=== Teorema: Gödel vence a Neumann
Si $f : D_f subset.eq omega^n times Sast^m -> O$ es $Sigma$-computable, entonces $f$ es $Sigma$-recursiva
(Hacer caso $O = Sast$)

*Prueba:*

Hipótesis: Sea $O = Sast$ y dado el programa $PP_0$ que computa a $f$.

$
  f = Phi^(n, m)_ast compose [p^(n,m)_1, ..., p^(n,m)_(n + m), C^(n, m)_PP_0]
$

donde $p^(n,m)_1, ..., p^(n,m)_(n + m)$ (respecto del alfabeto $Sigma union Sigma_p$) y $Phi^(n, m)_ast$ son $(Sigma union Sigma_p)$-recursivas.\
Por lo tanto $f$ es $(Sigma union Sigma_p)$-recursiva.\
Por "Teorema 4.2", $f$ es $Sigma$-recursiva.

=== Teorema: Caracterización de conjuntos $Sigma$-efectivamente computables
Sea $S subset.eq omega^n times Sast^m$. Son equivalentes:
+ $S$ es $Sigma$-efectivamente computable
+ $S$ y $(omega^n times Sast^m) - S$ son $Sigma$-efectivamente enumerables
(Hacer solo $arrow.l.double$)

*Prueba $arrow.l.double$:*

Hipótesis: Dado que $S subset.eq omega^n times Sast^m$ y $S$ y $(omega^n times Sast^m) - S$ son $Sigma$-efectivamente enumerables.

Si $S = emptyset$ o $S = omega^n times Sast^m$, entonces es claro que $S$ es $Sigma$-efectivamente computable.\

Supongamos que $S$ no es vacío ni $Sigma$-total.\
Por definición, existen procedimientos efectivos $PP_1$ y $PP_2$ que enumeran a $S$ y $(omega^n times Sast^m) - S$.\
El siguiente procedimiento efectivo computa a $chi^(omega^n times Sast^m)_S$:\

$
       & "Dada la entrada" (arrow(x), arrow(alpha)) in omega^n times Sast^m                           \
  E 1: & "Asignar a" T "el valor" 0                                                                   \
  E 2: & "  Realizar" PP_1 "con entrada" T "obteniendo" (arrow(y), arrow(beta))                       \
  E 3: & "  Realizar" PP_2 "con entrada" T "obteniendo" (arrow(z), arrow(gamma))                      \
  E 4: & "  Si" (arrow(x), arrow(alpha)) = (arrow(y), arrow(beta)) "entonces detenerse y devolver" 1  \
  E 5: & "  Si" (arrow(x), arrow(alpha)) = (arrow(z), arrow(gamma)) "entonces detenerse y devolver" 0 \
  E 6: & "  Asignar a" T "el valor" T + 1                                                             \
  E 7: & "  Saltar a" E 2
$

Por lo tanto, $S$ es $Sigma$-efectivamente computable.

== Combo 4
#ProposiciónCaracterizaciónbásicadeconjuntosSigmaenumerables

=== Lema: Lema de la sumatoria
Sea $Sigma$ un alfabeto finito. Si $f : omega times S_1 times ... times S_n times L_1 times ... times L_m -> omega$ es $Sigma$-pr, con $S_1, ..., S_n subset.eq omega$ y $L_1, ..., L_m subset.eq Sast$ no vacíos, entonces, la función $lambda x y arrow(x) arrow(alpha)[sum_(i=x)^y f(i, arrow(x), arrow(alpha))]$ es también $Sigma$-pr.

*Prueba:*

$
  lambda x y arrow(x) arrow(alpha) [sum_(i=x)^y f(i, arrow(x), arrow(alpha))] &= lambda y x arrow(x) arrow(alpha) [sum_(t=0)^(y) h(t, x, arrow(x), arrow(alpha))] compose [p^(2+n,m)_2, p^(2+n,m)_1, p^(2+n,m)_(3)...,p^(2+n,m)_(2+n+m)]\
  &= R(h,g) compose [p^(2+n,m)_2, p^(2+n,m)_1, p^(2+n,m)_(3)...,p^(2+n,m)_(2+n+m)]
$

Donde:

$
  h : omega times S_1 times ... times S_n times L_1 times ... times L_m &-> omega\
  (x, arrow(x), arrow(alpha)) &-> cases(0 &"si" (x, arrow(x), arrow(alpha)) in H_1, f(0, arrow(x), arrow(alpha)) &"si" (x, arrow(x), arrow(alpha)) in H_2)\
  g : omega^3 times S_1 times ... times S_n times L_1 times ... times L_m &-> omega\
  (A, t, x, arrow(x), arrow(alpha)) &-> cases(0 &"si" (A, t, x, arrow(x), arrow(alpha)) in G_1, A + f(t + 1, arrow(x), arrow(alpha)) &"si" (A, t, x, arrow(x), arrow(alpha)) in G_2)
$

Donde:

$
  H_1 & = {(x, arrow(x), arrow(alpha)) in "Dom"_h : x > 0}           \
  H_2 & = {(x, arrow(x), arrow(alpha)) in "Dom"_h : x = 0}           \
  G_1 & = {(A, t, x, arrow(x), arrow(alpha)) in "Dom"_g : x > t + 1} \
  G_2 & = {(A, t, x, arrow(x), arrow(alpha)) in "Dom"_g : x ≤ t + 1} \
$

Por "Lema 20" y "Lema 18", $h$ y $g$ son $Sigma$-pr.\

== Combo 5
=== Lema, Ejercicio de la Guía 5
Sean $Sigma = {@, %, !}$ y $S_1, S_2 subset.eq omega$ y $L_1, L_2 subset.eq Sast$ no vacíos.\
Sea $f : S_1 times S_2 times L_1 times L_2 -> omega$ y $rho.alt$ una familia $Sigma$-indexada de funciones $rho.alt_a : omega times S_1 times S_2 times L_1 times L_2 times Sast -> omega$ para cada $a in Sigma$.\
Si $f$ y cada $rho.alt_a$ son $Sigma$-efectivamente computables, entonces $R(f, rho.alt) : S_1 times S_2 times L_1 times L_2 times Sast -> omega$ lo es.

*Prueba:*

Por definición, existen procedimientos efectivos $PP_f$, $PP_rho.alt_@$, $PP_rho.alt_%$ y $PP_rho.alt_!$. \

El siguiente procedimiento efectivo computa a $R(f, rho.alt)$:

$
  &"Dada la entrada" (x, y, alpha, beta, gamma) in S_1 times S_2 times L_1 times L_2 times Sast \
  E 1: &"Asignar a" tau "el valor" epsilon \
  E 2: &"Asignar a" A "el resultado de correr" PP_f "con entrada" (x, y, alpha, beta)\
  E 3: &"  Si" gamma = epsilon "detenerse y devolver" A\
  E 4: &"  Si" [gamma]_1 = @, "Asignar a" A "el resultado de correr" PP_rho.alt_@ "con entrada" (A, x, y, alpha, beta, tau)\
  E 5: &"  Si" [gamma]_1 = %, "Asignar a" A "el resultado de correr" PP_rho.alt_% "con entrada" (A, x, y, alpha, beta, tau)\
  E 6: &"  Si" [gamma]_1 = !, "Asignar a" A "el resultado de correr" PP_rho.alt_! "con entrada" (A, x, y, alpha, beta, tau)\
  E 7: &"  Asignar a" tau "el resultado de correr" tau.[gamma]_1\
  E 8: &"  Asignar a" gamma "el resultado de correr" arrow.cw.half gamma\
  E 9: &"  Saltar a" E 3
$

=== Lema: Lema de cuantificación acotada
Sean $P : S times S_1 times ... times S_n times L_1 times ... times L_m -> {0, 1}$ y $overline(S) subset.eq S$ $Sigma$-pr.\
Entonces $lambda x arrow(x) arrow(alpha)[ (forall t in overline(S))_(t <= x) P(t, arrow(x), arrow(alpha))]$ es $Sigma$-pr

*Prueba:*

Sea:
$
  Q : omega times S_1 times ... times S_n times L_1 times ... times L_m &-> {0, 1}\
  (t, arrow(x), arrow(alpha)) &-> cases(P(t, arrow(x), arrow(alpha)) &"si" (t, arrow(x), arrow(alpha)) in overline(S), 1 &"si" (t, arrow(x), arrow(alpha)) in omega - overline(S))
$

Por "Lema 20" y "Lema 18", $Q$ es $Sigma$-pr.\

$
  lambda x arrow(x) arrow(alpha)[ (forall t in overline(S))_(t <= x) P(t, arrow(x), arrow(alpha))] &= lambda x arrow(x) arrow(alpha)[product^x_(t=0) Q(t, arrow(x), arrow(alpha))]\
  &= lambda z x arrow(x) arrow(alpha)[product^x_(t=z) Q(t, arrow(x), arrow(alpha))] compose [C^(1 + n, m)_0, p^(1 + n,m)_1, ..., p^(1 + n,m)_(1 + n + m)]
$

Por "Lema 22", es $Sigma$-pr.

== Combo 6
=== Lema:
Si $S subset.eq omega^n times Sast^m$ es $Sigma$-efectivamente computable, entonces $S$ es $Sigma$-efectivamente enumerable

*Prueba:*

Si $S = emptyset$, por definición $S$ es $Sigma$-efectivamente enumerable.\
Supongamos que $S$ no es vacío.\
Por definición existe un procedimiento efectivo  que computa a $chi^(omega^n times Sast^m)_S$.\
El siguiente procedimiento efectivo enumera a $S$:

$
       & "Dada la entrada" x in omega                                                                                     \
  E 1: & "Asignar a" arrow(x) "los resultados de correr" ((x))_1,...,((x))_n                                              \
  E 2: & "Asignar a" arrow(alpha) "los resultados de correr" ast^<= ((x))_1,..., ast^<= ((x))_n                           \
  E 3: & "Si" chi^(omega^n times Sast^m)_S (arrow(x), arrow(alpha)) = 1 "detenerse y devolver" (arrow(x), arrow(alpha))   \
  E 4: & "Asignar a" x "el valor" 0                                                                                       \
  E 5: & "  Asignar a" arrow(x) "los resultados de correr" ((x))_1,...,((x))_n                                            \
  E 6: & "  Asignar a" arrow(alpha) "los resultados de correr" ast^<= ((x))_1,..., ast^<= ((x))_n                         \
  E 7: & "  Si" chi^(omega^n times Sast^m)_S (arrow(x), arrow(alpha)) = 1 "detenerse y devolver" (arrow(x), arrow(alpha)) \
  E 8: & "  Asignar a" x "el resultado de correr" x + 1                                                                   \
  E 9: & "  Saltar a" E 5
$

Cada elemento en $S$ es equivalente a un posible estado de $(arrow(x), arrow(alpha))$ que tarde o temprano sera alcanzado.\
Ademas, dado que $S != emptyset$, el procedimiento efectivo siempre se detiene y devuelve un elemento de $S$.
Por lo tanto, $S$ es $Sigma$-efectivamente enumerable.

=== Teorema: Caracterización de conjuntos $Sigma$-r.e.
Sea $S subset.eq omega^n times Sast^m$. Son equivalentes:
+ $S$ es $Sigma$-recursivamente enumerable
+ $S = "Im"_F$, para alguna $F : "Dom"_F subset.eq omega^k times Sast^l -> omega^n times Sast^m$ tq cada $F(i)$ es $Sigma$-recursiva
+ $S = "Dom"_f$, para alguna función $Sigma$-recursiva $f$
(Hacer la prueba de $(2) -> (3)$, con $k = l = 1$ y $n = m = 2$)

*Prueba $=>$:*

Hipótesis: Dado $F : "Dom"_F subset.eq omega times Sast -> S subset.eq omega^2 times Sast^2$ sobreyectiva tq cada $F(i)$ es $Sigma$-recursiva.

Por teorema, existen programas $PP_i$ que computan $F_((i))$.\
Sea $<=$ un orden total sobre $Sigma$.\

Sea $"NotHalt"_PP_i = lambda t x alpha [ not "Halt"^(1,1)(t, x, alpha, PP_i) ]$\
Notar que, al abstraer $PP$, su dominio esta bajo $Sigma$, por lo que la función es $Sigma$-mixta.\
Por definición, $"Halt"^(1,1)$ es $(Sigma union Sigma_p)$-pr por lo que $"NotHalt"_PP_i$ también.\
Por "Teorema 4.2", $"NotHalt"_PP_i$ es $Sigma$-pr, por lo que es $Sigma$-computable y existe su macro.\

Definimos:
- $"NeqE"_(PP_i hash) = lambda z t x alpha [ y != E^(1,1)_(hash 1)(t, x, alpha, P_i)]$ para i = 1, 2
- $"NeqE"_(PP_i ast) = lambda x t alpha beta [ beta != E^(1,1)_(ast 1)(t, x, alpha, P_i)]$ para i = 3, 4
Notar que, al abstraer $PP$, sus dominios están bajo $Sigma$, por lo que las funciones son $Sigma$-mixtas.\
Por definición, $E^(1,1)_s$ son $(Sigma union Sigma_p)$-pr por lo que $"NeqE"_(PP_i s)$ también.\
Por "Teorema 4.2", $"NeqE"_(PP_i s)$ son $Sigma$-pr, por lo que son $Sigma$-computable y existen sus macros.\

Luego, para algún $j in NN$, $lambda x [(x)_j]$ y $lambda x [*^<= (x)_j]$ son $Sigma$-pr, por lo que son $Sigma$-computable y existen sus macros.\

$p^(2,2)_1|_S$ es una función tq $"Dom"_(p^(2,2)_1)|_S = S$. Demos un programa que la compute:

$
  L 1: & N 5 <- N 5 + 1                                         \
       & N 4 <- (N 5)_1                                         \
       & N 3 <- (N 5)_2                                         \
       & P 3 <- ast^(<=)((N 5)_3)                               \
       & ["IF" "NotHalt"_PP_1 (N 4, N 3, P 3) "GOTO" L 1]       \
       & ["IF" "NotHalt"_PP_2 (N 4, N 3, P 3) "GOTO" L 1]       \
       & ["IF" "NotHalt"_PP_3 (N 4, N 3, P 3) "GOTO" L 1]       \
       & ["IF" "NotHalt"_PP_4 (N 4, N 3, P 3) "GOTO" L 1]       \
       & ["IF" "NeqE"_(PP_1 hash) (N 1, N 4, N 3, P 3) "GOTO" L 1] \
       & ["IF" "NeqE"_(PP_2 hash) (N 2, N 4, N 3, P 3) "GOTO" L 1] \
       & ["IF" "NeqE"_(PP_3 ast) (P 1, N 4, N 3, P 3) "GOTO" L 1]  \
       & ["IF" "NeqE"_(PP_4 ast) (P 2, N 4, N 3, P 3) "GOTO" L 1]
$

Por lo tanto, $p^(2,2)_1|_S$ es $Sigma$-computable y $Sigma$-recursiva.\

== Combo 7
+ *Lema* (Lema de minimización acotada): Sean $n, m >= 0$. Sea $p : D_nu subset.eq omega times omega^n times Sast^m -> omega$ un predicado $Sigma$-pr
(a) $M(P)$ es $Sigma$-recursiva
(b) Si existe una función $f : omega^n times Sast^m -> omega$ $Sigma$-pr tq $M(P)(arrow(x), arrow(alpha)) = min_t P(t, arrow(x), arrow(alpha)) <= f(arrow(x), arrow(alpha))$, entonces $M(P)$ es $Sigma$-pr

+ *Lema*: Si $f : D_f subset.eq omega^n times Sast^m -> O$ es $Sigma$-recursiva y $S subset.eq D_f$ es $Sigma$-r.e., entonces $f|S$ es $Sigma$-recursiva
(Hacer solo el caso $S$ no vacío, $n = m = 1$ y $O = Sast$)

== Combo 8
+ *Lema*: Si $Sigma supset.eq Sigma_p$, entonces $"AutoHalt"^Sigma$ no es $Sigma$-recursivo

+ *Teorema*: Si $Sigma supset.eq Sigma_p$, entonces $"AutoHalt"^Sigma$ no es $Sigma$-efectivamente computable

+ *Lema*: Sea $A = p in "Pro"^Sigma : "AutoHalt"^Sigma(P) = 1$, entonces $A$ es $Sigma$-r.e. y no $Sigma$-recursivo
Además, el conjunto $N = p in "Pro"^Sigma : "AutoHalt"^Sigma(P) = 0$ no es $Sigma$-r.e.

+ *Teorema* (Neumann vence a Gödel): Si $h$ es $Sigma$-recursiva, entonces $h$ es $Sigma$-computable
(Hacer solo el caso $h = M(P)$)

== Combo 9
+ *Lema* (Lema de división por casos para funciones $Sigma$-recursivas): Supongamos $f_i : D_f_i subset.eq omega^n times Sast^m -> O$ para $i = 1, ..., k$, tales que $D_f_i arrow.r.double D_f_j = emptyset$ para $i != j$. Entonces $f_1 tack.r.double ... tack.r.double f_k$ es $Sigma$-recursiva
(Hacer el caso $k = 2$, $n = m = 1$ y $O = omega$)

+ *Teorema* (Gödel vence a Neumann): Si $f : D_f subset.eq omega^n times Sast^m -> omega$ es $Sigma$-computable, entonces $f$ es $Sigma$-recursiva

= Utilidades

== Lema 14.

Sean $P : S subset.eq omega^n times Sast^m -> {0, 1}$ y $Q : S subset.eq omega^n times Sast^m -> {0, 1}$ $Sigma$-pr, entonces también lo son: $(P or Q)$, $(P and Q)$ y $not P$.


== Def Conjuntos $Sigma$-pr
Un conjunto $Sigma$-mixto $S subset.eq omega^n times Sast^m$ se llama $Sigma$-recursivo primitivo si su función característica $chi^(omega^n times Sast^m)_S equiv lambda arrow(x) arrow(alpha) [ (arrow(x), arrow(alpha)) in S ]$ es $Sigma$-pr

== Lema 15.
Si $S_1, S_2 subset.eq omega^n times Sast^m$ son $Sigma$-pr, entonces también lo son:
$S_1 union S_2$, $S_1 inter S_2$ y $S_1 - S_2$.


== Lema 16.
Sean $S_1, ..., S_n subset.eq omega$ y $L_1, ..., L_m subset.eq Sast$ conjuntos no vacíos.

Entonces $S_1 times ... times S_n times L_1 times ... times L_m$ es $Sigma$-pr sii $S_1, ..., S_n, L_1, ..., L_m$ son $Sigma$-pr

== Lema 17.
Sea $f : "Dom"_f subset.eq omega^n times Sast^m -> O$ una función $Sigma$-pr.
Si $S subset.eq "Dom"_f$ es $Sigma$-pr, entonces la función $f|_S$ también es $Sigma$-pr

== Lema 18.
Si $f : "Dom"_f subset.eq omega^n times Sast^m -> O$ es $Sigma$-pr, entonces existe una función $overline(f) : omega^n times Sast^m -> O$ $Sigma$-pr tal que $f = overline(f)|_"Dom"_f$.

== Proposición 19.
#Proposición19
== Lema 20: Lema de division por casos para funciones $Sigma$-pr
#Lema20

== Lema 22.
Sea Sigma un alfabeto finito.

(a) Si  $f : omega times S_1 times ... times S_n times L_1 times ... times L_m -> omega$ es $Sigma$-pr, con $S_1, ..., S_n subset.eq omega$ y $L_1, ..., L_m subset.eq Sast$ no vacíos, entonces, las funciones $lambda x y arrow(x) arrow(alpha) . sum_(t=x)^y f(t, arrow(x), arrow(alpha))$  y $lambda x y arrow(x) arrow(alpha) . product_(t=x)^y f(t, arrow(x), arrow(alpha))$ son también $Sigma$-pr

(b) Si $f : omega times S_1 times ... times S_n times L_1 times ... times L_m -> Sast$ es $Sigma$-pr, con $S_1, ..., S_n subset.eq omega$ y $L_1, ..., L_m subset.eq Sast$ no vacíos, entonces la función $lambda x y arrow(x) arrow(alpha) . subset_(t=x)^y f(t, arrow(x), arrow(alpha))$ es $Sigma$-pr

== Proposición 4.8

Sea $f : "Dom"_f subset.eq omega^n times Sast^m -> omega$ una función $Sigma$-computable.
Entonces, en $S^Sigma$ hay un macro de la forma: $V overline(n+1) <- f(V 1, ..., V overline(n), W 1, ..., W overline(m))$

Sea $f : "Dom"_f subset.eq omega^n times Sast^m -> Sast$ una función $Sigma$-computable.
Entonces, en $S^Sigma$ hay un macro de la forma: $W overline(n+1) <- f(V 1, ..., V overline(n), W 1, ..., W overline(m))$

== Definición de función $Sigma$-computable
Una función $Sigma$-mixta $f : S subset.eq omega^n times Sast^m -> O$ será llamada $Sigma$-computable si hay un programa $P$ tal que $f = Psi^(n, m, s)_(P)$.


== Definición de conjuntos $Sigma$-enumerables

Un conjunto $S subset.eq omega^n times Sast^m$ será llamado $Sigma$-enumerable cuando sea vacío o exista una función sobreyectiva $F : omega -> S in omega^n times Sast^m$ y $F(i)$ sea $Sigma$-computable para cada $i in {1, ..., n + m}$.

== Teorema 4.2 (Independencia del alfabeto)

Sean $Sigma$ y $Gamma$ alfabetos cualesquiera:

+ (a) Supongamos que una función $f$ es $Sigma$-mixta y $Gamma$-mixta. Entonces $f$ es $Sigma$-recursiva (resp. $Sigma$-pr) sii $f$ es $Gamma$-recursiva (resp. $Gamma$-pr).

+ (b) Supongamos que un conjunto $S$ es $Sigma$-mixto y $Gamma$-mixto. Entonces $S$ es $Sigma$-recursivo (resp. $Sigma$-re, $Sigma$-pr) sii $S$ es $Gamma$-recursivo (resp. $Gamma$-re, $Gamma$-pr).
