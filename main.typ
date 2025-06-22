#import "template/main.typ": *

#show: it => basic-report(
  doc-category: "Lenguajes Formales y Computabilidad | FAMAF - UNC",
  doc-title: "Combos de definiciones y convenciones notacionales y los Combos de teoremas",
  author: "Matias Viola",
  heading-font: "Computer Modern",
  heading-color: black,
  it,
)

= Combos de definiciones y convenciones notacionales

== Combo 1
Defina:
=== Cuando un conjunto $S subset.eq omega^n times Sigma^*^m$ es llamado $Sigma$-recursivo

Un conjunto $S subset.eq omega^n times Sigma^*^m$ sera llamado $Sigma$-recursivo cuando la función $chi^(omega^n times Sigma^*^m)_S$ sea $Sigma$-recursiva. (version Godeliana del concepto de conjunto $Sigma$-efectivamente computable)

=== $angle.l s_1, s_2, ... angle.r$

Dada una infinitupla $(s_1, s_2, ...) ∈ omega^([N])$ usaremos $angle.l s_1, s_2, ... angle.r$ para denotar al numero $product^oo_(i=1) "pr"(i)^(s_i)$

=== "$f$ es una función $Sigma$-mixta"

Sea $Sigma$ un alfabeto finito. Una función $f$ es $Sigma$-mixta si:
+ $(exists n, m in omega) "Dom"_f subset.eq omega^n times Sigma^*^m$

+ $"Im"_f subset.eq O in {omega, Sigma^*}$

=== "familia $Sigma$-indexada de funciones"

Dado un alfabeto $Sigma$, una familia $Sigma$-indexada de funciones sera una función $G: Sigma arrow.r "Im"_G$ donde $"Im"_G$ es el conjunto de funciones $G(a)$ asociadas a cada $a in Sigma$.

NOTACION: Si $G$ es una familia $Sigma$-indexada de funciones, entonces para $a in Sigma$, escribiremos $G_a$ en lugar de $G(a)$.

=== $R(f, G)$: Recursion primitiva sobre variable alfabética con valores numéricos.

Sea una función $f : S_1 times ... times S_n times L_1 times ... times L_m arrow.r omega$ con $S_1, ..., S_n subset.eq omega$ y $L_1, ..., L_m subset.eq Sigma^*$ conjuntos no vacíos.

Sea una familia $Sigma$-indexada de funciones $G_a : omega times S_1 times ... times S_n times L_1 times ... times L_m times Sigma^* arrow.r omega$ para cada $a in Sigma$.

Definimos recursivamente la función $R(f, G) : S_1 times ... times S_n times L_1 times ... times L_m times Sigma^* arrow.r omega$ de la siguiente manera:
+ $R(f, G)(arrow(x), arrow(alpha), epsilon) = f(arrow(x), arrow(alpha))$
+ $R(f, G)(arrow(x), arrow(alpha), alpha a) = G_a (R(f, G)(arrow(x), arrow(alpha), alpha), arrow(x), arrow(alpha), alpha)$
También diremos que $R(f, g)$ es obtenida por recursion primitiva a partir de f y G.

== Combo 2
Defina:
+ $d tack.r^n d'$ y $d tack.r^* d'$ (no hace falta que defina $tack.r$)
+ $L(M)$
+ "f es una función de tipo $(n, m, s)$"
+ $(x)$
+ $(x)_i$

== Combo 3
Defina:
+ Cuando un conjunto $S subset.eq omega^n times Sigma^*^m$ es llamado $Sigma$-recursivamente enumerable (no hace falta que defina "función $Sigma$-recursiva")
+ $s^<=$
+ $ast^<=$
+ $"#"^<=$

== Combo 4
Defina cuando una función $f : D_f subset.eq omega^n times Sigma^*^m arrow.r omega$ es llamada $Sigma$-efectivamente computable y defina "el procedimiento $P$ computa a la función $f$"

== Combo 5
Defina cuando un conjunto $S subset.eq omega^n times Sigma^*^m$ es llamado $Sigma$-efectivamente computable y defina: "el procedimiento efectivo $P$ decide la pertenencia a $S$"

== Combo 6
Defina cuando un conjunto $S subset.eq omega^n times Sigma^*^m$ es llamado $Sigma$-efectivamente enumerable y defina: "el procedimiento efectivo $P$ enumera a $S$"

== Combo 7
Defina cuando una función $f : D_f subset.eq omega^n times Sigma^*^m arrow.r omega$ es llamada $Sigma$-Turing computable y defina "la máquina de Turing $M$ computa a la función $f$"

== Combo 8
Defina:
+ $M(P)$
+ $"Lt"$
+ Conjunto rectangular
+ "$S$ es un conjunto de tipo $(n, m)$"

== Combo 9
+ onjunto rectangular
+ "$I$ es una instrucción de $S^Sigma$"
+ "$P$ es un programa de $S^Sigma$"
+ $I^P_i$
+ $n(P)$
+ $"Bas"$

== Combo 10
Defina relativo al lenguaje $S^Sigma$:
+ "estado"
+ "descripción instantánea"
+ $S_P$
+ "estado obtenido luego de $t$ pasos, partiendo del estado $(arrow(x), arrow(alpha))$"
+ "$P$ se detiene (luego de $t$ pasos), partiendo desde el estado $(arrow(x), arrow(alpha))$"

== Combo 11
Defina:
+ $Psi^("n,m,#")_P$
+ "f es $Sigma$-computable"
+ "$P$ computa a $f$"
+ $M^<= (P)$

== Combo 12
Defina cuando un conjunto $S subset.eq omega^n times Sigma^*^m$ es llamado $Sigma$-computable, cuando es llamado $Sigma$-enumerable y defina "el programa $P$ enumera a $S$"

== Combo 13
Defina:
+ $i^(n,m)$
+ $E^(n,m)_"#"$ + $E^(n,m)_*$
+ $E^(n,m)_("#"j)$
+ $E^(n,m)_(*j)$
+ $"Halt"^(n,m)$
+ $T^(n,m)$
+ $"AutoHalt"^Sigma$
+ Los conjuntos $A$ y $N$

== Combo 14
Explique en forma detallada la notación lambda

== Combo 15
Dada una función $f : D_f subset.eq omega times Sigma^ast arrow.r omega$, describa qué tipo de objeto es y qué propiedades debe tener el macro: [V2 ← f(V1,W1)]

== Combo 16
Dado un predicado $P : D_f subset.eq omega times Sigma^ast arrow.r omega$, describa qué tipo de objeto es y qué propiedades debe tener el macro: [IF P(V1,W1) GOTO A1]

== Combo 17
Defina el concepto de función y desarrolle las tres Convenciones Notacionales asociadas a dicho concepto (Guía 1)

= Combos de teoremas

== Combo 1
+ *Proposición* (Caracterización de conjuntos $Sigma$-p.r.): Un conjunto $S$ es $Sigma$-p.r. sii $S$ es el dominio de alguna función $Sigma$-p.r. (En la inducción de la prueba hacer solo el caso de la composición)

+ *Teorema* (Neumann vence a Gödel): Si $h$ es $Sigma$-recursiva, entonces $h$ es $Sigma$-computable. (En la inducción de la prueba hacer solo el caso $h = R(f, G)$, con $I_h subset.eq omega$)

== Combo 2
+ *Lema* (Lema de división por casos para funciones $Sigma$-p.r.): Supongamos $f_i : D_f_i subset.eq omega^n times Sigma^*^m arrow.r Sigma^*$, $i = 1, ..., k$, son funciones $Sigma$-p.r. tales que $D_f_i inter D_f_j = emptyset$ para $i != j$. Entonces $f_1 inter ... inter f_k$ es $Sigma$-p.r. (Hacer el caso $k = 2$, $n = 2$ y $m = 1$)

+ *Proposición* (Caracterización básica de conjuntos $Sigma$-enumerables): Sea $S subset.eq omega^n times Sigma^*^m$ un conjunto no vacío. Entonces son equivalentes:
  + $S$ es $Sigma$-enumerable
  + Hay un programa $P in "Pro"^Sigma$ tal que:
    + Para cada $x in omega$, $P$ se detiene partiendo desde el estado $⟦x⟧$ y llega a un estado de la forma $((x_1, ..., x_n, y_1, ...), (alpha_1, ..., alpha_m, beta_1, ...))$, donde $(x_1, ..., x_n, alpha_1, ..., alpha_m) in S$
    + Para cada $(x_1, ..., x_n, alpha_1, ..., alpha_m) in S$ hay un $x in omega$ tal que $P$ se detiene partiendo desde el estado $⟦x⟧$ y llega a un estado como en $((x_1, ..., x_n, y_1, ...), (alpha_1, ..., alpha_m, beta_1, ...))$
(Hacer el caso $n = 2$ y $m = 1$)

== Combo 3
+ *Teorema* (Gödel vence a Neumann): Si $f : D_f subset.eq omega^n times Sigma^*^m arrow.r Sigma^*$ es $Sigma$-computable, entonces $f$ es $Sigma$-recursiva

+ *Teorema* (Caracterización de conjuntos $Sigma$-efectivamente computables): Sea $S subset.eq omega^n times Sigma^*^m$. Son equivalentes:
(a) $S$ es $Sigma$-efectivamente computable
(b) $S$ y $(omega^n times Sigma^*^m) - S$ son $Sigma$-efectivamente enumerables
(Hacer solo $(b) arrow.r (a)$)

== Combo 4
+ *Proposición* (Caracterización básica de conjuntos $Sigma$-enumerables): (igual a Combo 2, hacer caso $n = 2$, $m = 1$)

+ *Lema* (Lema de la sumatoria): Sea $Sigma$ un alfabeto finito. Si $f : omega times S_1 times ... times S_n times L_1 times ... times L_m arrow.r omega$ es $Sigma$-p.r., con $S_i subset.eq omega$ y $L_j subset.eq Sigma^*$ no vacíos, entonces
$lambda x y arrow(x) arrow(alpha). sum_t=x^y f(t, arrow(x), arrow(alpha))$ es $Sigma$-p.r.

== Combo 5
+ *Lema*: Sea $Sigma = @, %, !$ y $f : S_1 times S_2 times L_1 times L_2 arrow.r omega$, con $S_1, S_2 subset.eq omega$ y $L_1, L_2 subset.eq Sigma^*$ no vacíos. Sea $G$ una familia $Sigma$-indexada de funciones $G_a : omega times S_1 times S_2 times L_1 times L_2 times Sigma^* arrow.r omega$ para cada $a in Sigma$.
Si $f$ y cada $G_a$ son $Sigma$-efectivamente computables, entonces $R(f, G)$ lo es.
(Ejercicio de la Guía 5)

+ *Lema* (Lema de cuantificación acotada): Sea $P : S times S_1 times ... times S_n times L_1 times ... times L_m arrow.r omega$ un predicado $Sigma$-p.r., y $dash(S) subset.eq S$ un conjunto $Sigma$-p.r. Entonces
$lambda x arrow(x) arrow(alpha)[ (forall t in dash(S))_(t <= x) P(t, arrow(x), arrow(alpha))]$ es $Sigma$-p.r.

== Combo 6
+ *Lema*: Si $S subset.eq omega^n times Sigma^*^m$ es $Sigma$-efectivamente computable, entonces $S$ es $Sigma$-efectivamente enumerable

+ *Teorema* (Caracterización de conjuntos $Sigma$-r.e.): Sea $S subset.eq omega^n times Sigma^*^m$. Son equivalentes:
(1) $S$ es $Sigma$-recursivamente enumerable
(2) $S = "IF"$, para alguna $F : D_F subset.eq omega^k times Sigma^*^l arrow.r omega^n times Sigma^*^m$ tal que cada $F(i)$ es $Sigma$-recursiva
(3) $S = D_f$, para alguna función $Sigma$-recursiva $f$
(Hacer la prueba de $(2) arrow.r (3)$, con $k = l = 1$ y $n = m = 2$)

== Combo 7
+ *Lema* (Lema de minimización acotada): Sean $n, m >= 0$. Sea $P : D_P subset.eq omega times omega^n times Sigma^*^m arrow.r omega$ un predicado $Sigma$-p.r.
(a) $M(P)$ es $Sigma$-recursiva
(b) Si existe una función $f : omega^n times Sigma^*^m arrow.r omega$ $Sigma$-p.r. tal que $M(P)(arrow(x), arrow(alpha)) = min_t P(t, arrow(x), arrow(alpha)) <= f(arrow(x), arrow(alpha))$, entonces $M(P)$ es $Sigma$-p.r.

+ *Lema*: Si $f : D_f subset.eq omega^n times Sigma^*^m arrow.r O$ es $Sigma$-recursiva y $S subset.eq D_f$ es $Sigma$-r.e., entonces $f|S$ es $Sigma$-recursiva
(Hacer solo el caso $S$ no vacío, $n = m = 1$ y $O = Sigma^*$)

== Combo 8
+ *Lema*: Si $Sigma supset.eq Sigma_p$, entonces $"AutoHalt"^Sigma$ no es $Sigma$-recursivo

+ *Teorema*: Si $Sigma supset.eq Sigma_p$, entonces $"AutoHalt"^Sigma$ no es $Sigma$-efectivamente computable

+ *Lema*: Sea $A = P in "Pro"^Sigma : "AutoHalt"^Sigma(P) = 1$, entonces $A$ es $Sigma$-r.e. y no $Sigma$-recursivo
Además, el conjunto $N = P in "Pro"^Sigma : "AutoHalt"^Sigma(P) = 0$ no es $Sigma$-r.e.

+ *Teorema* (Neumann vence a Gödel): Si $h$ es $Sigma$-recursiva, entonces $h$ es $Sigma$-computable
(Hacer solo el caso $h = M(P)$)

== Combo 9
+ *Lema* (Lema de división por casos para funciones $Sigma$-recursivas): Supongamos $f_i : D_f_i subset.eq omega^n times Sigma^*^m arrow.r O$ para $i = 1, ..., k$, tales que $D_f_i arrow.r.double D_f_j = emptyset$ para $i != j$. Entonces $f_1 tack.r.double ... tack.r.double f_k$ es $Sigma$-recursiva
(Hacer el caso $k = 2$, $n = m = 1$ y $O = omega$)

+ *Teorema* (Gödel vence a Neumann): Si $f : D_f subset.eq omega^n times Sigma^*^m arrow.r omega$ es $Sigma$-computable, entonces $f$ es $Sigma$-recursiva
