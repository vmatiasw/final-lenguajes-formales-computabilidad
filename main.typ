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

= Combos de definiciones y convenciones notacionales

== Combo 1: Defina:
=== Cuando un conjunto $S subset.eq omega^n times Sast^m$ es llamado $Sigma$-recursivo

Un conjunto $S subset.eq omega^n times Sast^m$ sera llamado $Sigma$-recursivo cuando la función $chi^(omega^n times Sast^m)_S$ sea $Sigma$-recursiva.

=== $angle.l s_1, s_2, ... angle.r$

Dada una infinitupla $(s_1, s_2, ...) ∈ omega^([NN])$ usaremos $angle.l s_1, s_2, ... angle.r$ para denotar al numero $product^oo_(i=1) "pr"(i)^(s_i)$

=== "$f$ es una función $Sigma$-mixta"

Sea $Sigma$ un alfabeto finito. Una función $f$ es $Sigma$-mixta si:
+ $(exists n, m in omega) "Dom"_f subset.eq omega^n times Sast^m$

+ $"Im"_f subset.eq O in {omega, Sast}$

=== "familia $Sigma$-indexada de funciones"

Dado un alfabeto $Sigma$, una familia $Sigma$-indexada de funciones sera una función $G: Sigma -> "Im"_G$ donde $"Im"_G$ es el conjunto de funciones $G(a)$ asociadas a cada $a in Sigma$.

NOTACIÓN: Si $G$ es una familia $Sigma$-indexada de funciones, entonces para $a in Sigma$, escribiremos $G_a$ en lugar de $G(a)$.

=== $R(f, G)$: Recursion primitiva sobre variable alfabética con valores numéricos.

Sea una función $f : S_1 times ... times S_n times L_1 times ... times L_m -> omega$ con $S_1, ..., S_n subset.eq omega$ y $L_1, ..., L_m subset.eq Sast$ conjuntos no vacíos.

Sea una familia $Sigma$-indexada de funciones $G_a : omega times S_1 times ... times S_n times L_1 times ... times L_m times Sast -> omega$ para cada $a in Sigma$.

Definimos recursivamente la función $R(f, G) : S_1 times ... times S_n times L_1 times ... times L_m times Sast -> omega$ de la siguiente manera:
+ $R(f, G)(arrow(x), arrow(alpha), epsilon) = f(arrow(x), arrow(alpha))$
+ $R(f, G)(arrow(x), arrow(alpha), alpha a) = G_a (R(f, G)(arrow(x), arrow(alpha), alpha), arrow(x), arrow(alpha), alpha)$
También diremos que $R(f, g)$ es obtenida por recursion primitiva a partir de f y G.

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

Sea $O in {omega, Sast}$. Una función $Sigma$-mixta $f : "Dom"_f subset.eq omega^n times Sast^m -> O$ sera llamada $Sigma$-efectivamente computable si hay un procedimiento efectivo $P$ tq
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
(i, P) &-> "i-esima instrucción de P contando desde el 1. " &"si" i in {1, ..., n(P)}\
(i, P) &-> epsilon &"si" i in.not {1, ..., n(P)}$

=== $n(P)$

$lambda P [n(P)] : "Pro"^Sigma &-> omega\
P &-> m "tq" P = I_1 I_2...I_m$

=== $"Bas"$

$"Bas" : "Ins"^Sigma &-> (Sigma union Sigma_p)^ast\
I &-> J &"si" I "es de la forma" L overline(k) J "con" J in "Ins"^Sigma\
I &-> I &"c.c."$

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
(i, arrow(x), arrow(sigma)) &-> (i, arrow(x), arrow(sigma)) &"si" i in.not {1, ..., n(P)}\
(i, arrow(s), arrow(sigma)) &-> (i + 1, (s_1, ..., s_k - 1, ...), arrow(sigma)) &"si" "Bas"(I^P_i) = N overline(k) <- N overline(k) - 1\
(i, arrow(s), arrow(sigma)) &-> (i + 1, (s_1, ..., s_k + 1, ...), arrow(sigma)) &"si" "Bas"(I^P_i) = N overline(k) <- N overline(k) + 1\
(i, arrow(s), arrow(sigma)) &-> (i + 1, (s_1, ..., s_n, ...), arrow(sigma)) &"si" "Bas"(I^P_i) = N overline(k) <- N overline(n)\
(i, arrow(s), arrow(sigma)) &-> (i + 1, (s_1, ..., 0, ...), arrow(sigma)) &"si" "Bas"(I^P_i) = N overline(k) <- 0\
(i, arrow(s), arrow(sigma)) &-> (i + 1, arrow(s), arrow(sigma)) &"si" "Bas"(I^P_i) = "IF" N overline(k) != 0 "GOTO" L overline(m) and s_k = 0\
(i, arrow(s), arrow(sigma)) &-> (min { l : I^P_l "tiene label" L overline(m) }, arrow(s), arrow(sigma)) &"si" "Bas"(I^P_i) = "IF" N overline(k) != 0 "GOTO" L overline(m) and s_k != 0\
(i, arrow(s), arrow(sigma)) &-> (i + 1, arrow(s), (sigma_1, ..., arrow.cw.half sigma_k, ...)) &"si" "Bas"(I^P_i) = P overline(k) <- arrow.cw.half P overline(k)\
(i, arrow(s), arrow(sigma)) &-> (i + 1, arrow(s), (sigma_1, ..., sigma_k a, ...)) &"si" "Bas"(I^P_i) = P overline(k) <- P overline(k) . a\
(i, arrow(s), arrow(sigma)) &-> (i + 1, arrow(s), (sigma_1, ..., sigma_macron(n), ...)) &"si" "Bas"(I^P_i) = P overline(k) <- P overline(n)\
(i, arrow(s), arrow(sigma)) &-> (i + 1, arrow(s), (sigma_1, ..., epsilon , ...)) &"si" "Bas"(I^P_i) = P overline(k) <- epsilon\
(i, arrow(s), arrow(sigma)) &-> (min { l : I^P_l "tiene label" L overline(m) }, arrow(s), arrow(sigma)) &"si" "Bas"(I^P_i) = "IF" P overline(k) "BEGINS" a "GOTO" L overline(m) and [sigma_k]_1 = a\
(i, arrow(s), arrow(sigma)) &-> (i + 1, arrow(s), arrow(sigma)) &"si" "Bas"(I^P_i) = "IF" P overline(k) "BEGINS" a "GOTO" L overline(m) and [sigma_k]_1 != a\
(i, arrow(s), arrow(sigma)) &-> (min { l : I^P_l "tiene label" L overline(m) }, arrow(s), arrow(sigma)) &"si" "Bas"(I^P_i) = "GOTO" L overline(m)\
(i, arrow(s), arrow(sigma)) &-> (i + 1, arrow(s), arrow(sigma)) &"si" "Bas"(I^P_i) = "SKIP"$


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
total sobre $Sigma$, $<=$ puede ser naturalmente extendido a un orden total sobre $Sast$. Sea $P : "Dom"_P subset.eq omega^n times Sast^m times Sast$ un predicado. Cuando $(arrow(x), arrow(alpha)) in omega^n times Sast^m$ es tq existe al menos un $alpha in Sast$ tq $P(arrow(x), arrow(alpha), alpha) = 1$, usaremos $min^<=_{alpha} P(arrow(x), arrow(alpha), alpha)$ para denotar al menor $alpha in Sast$ tq $P(arrow(x), arrow(alpha), alpha) = 1$.

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

Dada una función $f : "Dom"_f subset.eq omega^n times Sast^m arrow.r omega$ $Sigma$-computable, escribiremos $V overline(n+1) <- f(V 1, ..., V overline(n), W 1, ..., W overline(m))$ para denotar un macro $M$ que cumple las propiedades:

+ Las variables oficiales de $M$ son:
  $V 1, ..., V overline(n), V overline(n+1), W 1, ..., W overline(m)$
+ $M$ no tiene labels oficiales.
+ Si reemplazamos:
  + Las variables oficiales por variables concretas $N overline(k_1), ..., N overline(k_n), N overline(k_(n+1)), P overline(j_1), ..., P overline(j_m)$
  + Las variables auxiliares de $M$ por variables concretas todas distintas entre sí y distintas de las ya mencionadas.
  + Los labels auxiliares por labels concretos, también distintos entre sí.

  Entonces, la palabra así obtenida es un programa de $S^Sigma$ que denotamos $N overline(k_(n+1)) <- f(N overline(k_1), ..., N overline(k_n), P overline(j_1), ..., P overline(j_m))$ y debe satisfacer que si lo corremos partiendo de un estado $e$ que le asigne a las variables $N overline(k_1), ..., N overline(k_n), N overline(k_(n+1)), P overline(j_1), ..., P overline(j_m)$ valores $x_1 , ..., x_n , alpha_1 , ..., alpha_m$ , entonces independientemente de los valores que les asigne $e$ al resto de las variables se dará que:

  + Si $(arrow(x), arrow(alpha)) in.not "Dom"_f$, entonces el programa no se detiene.
  + Si $(arrow(x), arrow(alpha)) in "Dom"_f$, entonces:
    - El programa se detiene;
    - Llega a un estado $e'$ tq:
      + $e'$ asigna a $N overline(k_(n+1))$ el valor $f(arrow(x), arrow(alpha))$;
      + $e'$ solo difiere de $e$ en el valor de $N overline(k_(n+1))$ y en aquellas variables que reemplazaron a las variables auxiliares de $M$. 

La palabra $N overline(k_(n+1)) <- f(N overline(k_1), ..., N overline(k_n), P overline(j_1), ..., P overline(j_m))$ se denomina la expansión del macro $V overline(n+1) <- f(V 1, ..., V overline(n), W 1, ..., W overline(m))$ respecto de la elección concreta de variables y labels realizada.

== Combo 16: Dado un predicado $p : D_f subset.eq omega times Sast -> omega$, describa qué tipo de objeto es y qué propiedades debe tener el macro: [IF P(V1,W1) GOTO A1]

Dado un predicado $P : "Dom"_P subset.eq omega^n times Sast^m -> {0, 1}$ $Sigma$-computable, escribiremos $["IF" P(V 1, ..., V overline(n), W 1, ..., W overline(m)) "GOTO" A 1]$ para denotar un macro $M$ que cumple las siguientes propiedades:

+ Las variables oficiales de $M$ son: $V 1, ..., V overline(n), W 1, ..., W overline(m)$
+ $A 1$ es el único label oficial de $M$.
+ Si reemplazamos:
  + Las variables oficiales por variables concretas:  
    $N overline(k_1), ..., N overline(k_n), P overline(j_1), ..., P overline(j_m)$
  + El label oficial $A 1$ por un label concreto $L overline(k)$
  + Las variables auxiliares por variables concretas, todas distintas entre sí y distintas de las ya mencionadas
  + Los labels auxiliares por labels concretos, todos distintos entre sí y distintos de $L overline(k)$

  Entonces, la palabra así obtenida es un programa de $S^Sigma$ (salvo por la ley del GOTO respecto de $L overline(k)$) que denotaremos $["IF" P(N overline(k_1), ..., N overline(k_n), P overline(j_1), ..., P overline(j_m)) "GOTO" L overline(k)]$ y debe satisfacer que si lo corremos partiendo de un estado $e$ que le asigne a las variables $N overline(k_1), ..., N overline(k_n), P overline(j_1), ..., P overline(j_m)$ valores $x_1 , ..., x_n , alpha_1 , ..., alpha_m$ , entonces independientemente de los valores que les asigne $e$ al resto de las variables se dará que
    + Si $(arrow(x), arrow(alpha)) in.not "Dom"_P$, el programa no se detiene.
    + Si $(arrow(x), arrow(alpha)) in "Dom"_P$ y $P(arrow(x), arrow(alpha)) = 1$, entonces:
      - Luego de una cantidad finita de pasos, se salta al label $L overline(k)$.
      - El estado alcanzado $e'$ también solo puede diferir de $e$ en las variables que reemplazaron a las auxiliares de $M$, y no modifica las demás.
    + Si $(arrow(x), arrow(alpha)) in "Dom"_P$ y $P(arrow(x), arrow(alpha)) = 0$, entonces:
      - Luego de una cantidad finita de pasos, el programa se detiene.
      - El estado alcanzado $e'$ también solo puede diferir de $e$ en las variables que reemplazaron a las auxiliares de $M$, y no modifica las demás.

La palabra $["IF" P(N overline(k_1), ..., N overline(k_n), P overline(j_1), ..., P overline(j_m)) "GOTO" L overline(k)]$ se denomina la expansión del macro $["IF" P(V 1, ..., V overline(n), W 1, ..., W overline(m)) "GOTO" A 1]$ respecto de la elección concreta de variables y labels realizada.


== Combo 17: Defina el concepto de función y desarrolle las tres Convenciones Notacionales asociadas a dicho concepto

Una función es un conjunto de pares tq, si $(x, y) in f$ y $(x, z) in f$, entonces $y = z$.

Dada una función $f$, definimos:
- $"Dom"_f = {x : (x, y) in f "para algún" y}$
- $"Im"_f = {y : (x, y) in f "para algún" x}$

Dado $x in "Dom"_f$, usaremos $f (x)$ para denotar al único $y in "Im"_f$ tq $(x, y) in f$.

Nótese que $emptyset$ es una función y que
$"Dom"_emptyset = "Im"_emptyset = emptyset$.

Escribimos $f : S subset.eq A -> B$ para expresar que $f$ es una función tq $"Dom"_f = S subset.eq A$ y $"Im"_f subset.eq B$. También escribimos $f : A -> B$ si $S = A$. En tal contexto llamaremos a $B$ conjunto de llegada.

Muchas veces para definir una función $f$, lo haremos dando su dominio y su regla de asignación.

Ademas, para hacer mas intuitiva aun la descripción de la función, también incluiremos un conjunto de llegada de dicha función y a la regla de asignación la escribiremos usando una flecha.

= Combos de teoremas

== Combo 1
+ *Proposición* (Caracterización de conjuntos $Sigma$-p.r.): Un conjunto $S$ es $Sigma$-p.r. sii $S$ es el dominio de alguna función $Sigma$-p.r. (En la inducción de la prueba hacer solo el caso de la composición)

+ *Teorema* (Neumann vence a Gödel): Si $h$ es $Sigma$-recursiva, entonces $h$ es $Sigma$-computable. (En la inducción de la prueba hacer solo el caso $h = R(f, G)$, con $I_h subset.eq omega$)

== Combo 2
+ *Lema* (Lema de división por casos para funciones $Sigma$-p.r.): Supongamos $f_i : D_f_i subset.eq omega^n times Sast^m -> Sast$, $i = 1, ..., k$, son funciones $Sigma$-p.r. tales que $D_f_i inter D_f_j = emptyset$ para $i != j$. Entonces $f_1 inter ... inter f_k$ es $Sigma$-p.r. (Hacer el caso $k = 2$, $n = 2$ y $m = 1$)

+ *Proposición* (Caracterización básica de conjuntos $Sigma$-enumerables): Sea $S subset.eq omega^n times Sast^m$ un conjunto no vacío. Entonces son equivalentes:
  + $S$ es $Sigma$-enumerable
  + Hay un programa $P in "Pro"^Sigma$ tq:
    + Para cada $x in omega$, $P$ se detiene partiendo desde el estado $⟦x⟧$ y llega a un estado de la forma $((x_1, ..., x_n, y_1, ...), (alpha_1, ..., alpha_m, beta_1, ...))$, donde $(x_1, ..., x_n, alpha_1, ..., alpha_m) in S$
    + Para cada $(x_1, ..., x_n, alpha_1, ..., alpha_m) in S$ hay un $x in omega$ tq $P$ se detiene partiendo desde el estado $⟦x⟧$ y llega a un estado como en $((x_1, ..., x_n, y_1, ...), (alpha_1, ..., alpha_m, beta_1, ...))$
(Hacer el caso $n = 2$ y $m = 1$)

== Combo 3
+ *Teorema* (Gödel vence a Neumann): Si $f : D_f subset.eq omega^n times Sast^m -> Sast$ es $Sigma$-computable, entonces $f$ es $Sigma$-recursiva

+ *Teorema* (Caracterización de conjuntos $Sigma$-efectivamente computables): Sea $S subset.eq omega^n times Sast^m$. Son equivalentes:
(a) $S$ es $Sigma$-efectivamente computable
(b) $S$ y $(omega^n times Sast^m) - S$ son $Sigma$-efectivamente enumerables
(Hacer solo $(b) -> (a)$)

== Combo 4
+ *Proposición* (Caracterización básica de conjuntos $Sigma$-enumerables): (igual a Combo 2, hacer caso $n = 2$, $m = 1$)

+ *Lema* (Lema de la sumatoria): Sea $Sigma$ un alfabeto finito. Si $f : omega times S_1 times ... times S_n times L_1 times ... times L_m -> omega$ es $Sigma$-p.r., con $S_i subset.eq omega$ y $L_j subset.eq Sast$ no vacíos, entonces
$lambda x y arrow(x) arrow(alpha). sum_t=x^y f(t, arrow(x), arrow(alpha))$ es $Sigma$-p.r.

== Combo 5
+ *Lema*: Sea $Sigma = @, %, !$ y $f : S_1 times S_2 times L_1 times L_2 -> omega$, con $S_1, S_2 subset.eq omega$ y $L_1, L_2 subset.eq Sast$ no vacíos. Sea $G$ una familia $Sigma$-indexada de funciones $G_a : omega times S_1 times S_2 times L_1 times L_2 times Sast -> omega$ para cada $a in Sigma$.
Si $f$ y cada $G_a$ son $Sigma$-efectivamente computables, entonces $R(f, G)$ lo es.
(Ejercicio de la Guía 5)

+ *Lema* (Lema de cuantificación acotada): Sea $p : S times S_1 times ... times S_n times L_1 times ... times L_m -> omega$ un predicado $Sigma$-p.r., y $dash(S) subset.eq S$ un conjunto $Sigma$-p.r. Entonces
$lambda x arrow(x) arrow(alpha)[ (forall t in dash(S))_(t <= x) P(t, arrow(x), arrow(alpha))]$ es $Sigma$-p.r.

== Combo 6
+ *Lema*: Si $S subset.eq omega^n times Sast^m$ es $Sigma$-efectivamente computable, entonces $S$ es $Sigma$-efectivamente enumerable

+ *Teorema* (Caracterización de conjuntos $Sigma$-r.e.): Sea $S subset.eq omega^n times Sast^m$. Son equivalentes:
(1) $S$ es $Sigma$-recursivamente enumerable
(2) $S = "IF"$, para alguna $F : D_F subset.eq omega^k times Sast^l -> omega^n times Sast^m$ tq cada $F(i)$ es $Sigma$-recursiva
(3) $S = D_f$, para alguna función $Sigma$-recursiva $f$
(Hacer la prueba de $(2) -> (3)$, con $k = l = 1$ y $n = m = 2$)

== Combo 7
+ *Lema* (Lema de minimización acotada): Sean $n, m >= 0$. Sea $p : D_nu subset.eq omega times omega^n times Sast^m -> omega$ un predicado $Sigma$-p.r.
(a) $M(P)$ es $Sigma$-recursiva
(b) Si existe una función $f : omega^n times Sast^m -> omega$ $Sigma$-p.r. tq $M(P)(arrow(x), arrow(alpha)) = min_t P(t, arrow(x), arrow(alpha)) <= f(arrow(x), arrow(alpha))$, entonces $M(P)$ es $Sigma$-p.r.

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
