#import "@preview/theorion:0.6.0": *
#import cosmos.rainbow: *
#show: show-theorion

#outline(title: none)

#show math.equation: set text(size: 1.1em)

= Ряды
= Ряды в нормированных пространствах
#definition[
$X$ норм. простр. $sum_(n=1)^oo x_n$ - ряд \
Частичная сумма $S_n := sum_(n=1)^n x_n$ \
Если существует предел $lim S_n$, то он называется суммой ряда, а ряд называется сходящимся
]
#warning-block[
В нормированом пространстве $RR$ нет $plus.minus oo$, поэтому ряд сходится $<=> lim S_n$ существует и конечен
]
#theorem[
Если ряд $sum_(n=1)^oo x_n$ сходится, то: $ lim x_n = 0 $
]
#proof[
Пусть $S$ - сумма ряда, тогда $lim S_n = S$ и предел $ lim x_n = lim (S_n - S_(n-1)) = lim S_n - lim S_(n-1) = S - S = 0 $
]
#property[
+ Линейность. Если $sum_(n=1)^oo x_n$ и сходятся $sum_(n=1)^oo y_n$ сходятся, $alpha, beta in RR$, то ряд $sum_(n=1)^oo (alpha x_n + beta y_n)$ сходится и его сумма $ sum (alpha x_n + beta x_n) = alpha sum x_n + beta sum y_n $ 

+ Изменение конечного числа членов последовательности не влияет на сходимость


+ Если ряд сходится, то расстановка скобок не меняет сумму. Расстановка скобок = выбор подпоследовательности в последовательности частичных сумм.

+ В $CC$ и $RR^d$ сходимость ряда означает сходимость числовых рядов составленных для каждой координаты отдельно
]
#theorem[Критерий Коши для сходимости рядов][
$X$ - полное нормированное пространство. Тогда следующие условия равносильны:
+ Ряд сходящийся
+ $forall epsilon: exists N: forall n > m >= N: norm(sum_(k=m+1)^n) < epsilon$
]
#proof[
1.$<=>$ $S_n$ имеет предел в $X$, а существование предела равносильно фундаментальности, то есть $forall epsilon > 0: exists N: forall n, m >= N: norm(S_n - S_m) < epsilon$, а это одно и то же с условием
]
#definition[
ряд $sum_(n=1)^oo x_n$ называется абсолютно сходящимся, если числовой ряд $sum_(n=1)^oo norm(x_n)$ сходится
]
#note[
В $RR$ абсолютная сходимость означает, что $sum_(n=1)^oo abs(x_n)$ сходится
]
#theorem[
$X$ - полное нормированное пространство. Если ряд $sum x_n$ абсолютно сходится, то он сходится
]
#proof[
$ sum_(n=1)^oo norm(x_n) "сходится" <==>_"кр. Коши" forall epsilon > 0: exists N: forall n > m >= N: sum_(k=m+1)^n norm(x_k) < epsilon, norm(sum_(k=m+1)^n x_n)<= sum_(k=m+1)^n norm(x_k)< epsilon $ $ => forall epsilon >0: exists N: forall n > m >= N => norm(sum_(k=m+1)^n x_k) < epsilon $

$<=>$ по критерию коши $sum_(n=1)^oo x_n$ - сходится
]
#corollary[
Если ряд $sum x_n$ абсолютно сходится, то $norm(sum_(n=1)^oo x_n ) <= sum_(n=1)^oo norm(x_n)$
]
#proof[
$ S_k:= sum_(k=1)^n x_k -> S:= sum_(k=1)^oo x_k $  \
$ norm(S_n) <= sum_(k=1)^n norm(x_k) -->_(n->oo) sum_(k=1)^oo norm(x_k) $
]
#exercise[
+ Доказать, что если в норм. пространстве для любого ряда выполняется критерий Коши, то $X$ полное
+ Доказать, что если в нормированном пространстве $X$ любой абсолютно сход. ряд сходится, то $X$ полное
]
== Когда из сходимости сгруппированного ряда следует сходимость исходного?
#theorem[
$sum_(n=1)^oo x_n$ ряд в нормированном пространстве $X$. Если
+ $lim x_n = 0$
+ сгруппированный ряд сходится
+ в каждой группе $<= K$ слагаемых
Тогда исходный ряд сходится
]
#proof[
  
$S_n_k$ - подпоследовательность частичных сумм, которая образовалась после группировки, знаем, что $S_n_k -->_(k->oo) S, n_1 < n_2 < n_3 < dots$ $n_(k+1) - n_k <= K$ количество слагаемых в $k+1$ группе

Рассмотрим сумму $S_n$, найдем $k$, такое  что $n_k <= n < n_(k+1)$: $S_n = S_n_k + x_(n_k + 1) + x_(n_k + 2) + dots x_n$ 

$norm(S_n - S) <= norm(S_n_k - S) + norm(x_(n_k + 1)) + dots + norm(x_n)$

Возьмем $epsilon > 0$

$lim S_n_k = S => exists M$, такоe что $forall k >= M: norm(S_n_k - S) < epsilon$

$lim x_n = 0 => exists N$, такое что $forall n >= N: norm(x_n) < epsilon$

Возьмем $n>= max{N, n_M}$ тогда 


$norm(S_n - S) <= underbrace(norm(S_n_k - S), < epsilon)+ underbrace(norm(x_(n_k + 1)), <epsilon ) + dots + underbrace(norm(x_n), < epsilon ) < K dot epsilon$
]

#theorem[
$sum_(n=1)^oo x_n$ числовой ряд. Если сгруппированный ряд сходится и в каждой группе все члены имеют один и тот же знак, то исходный ряд тоже сходится
]
#proof[
$S_n_k$ последовательность частичных сумм сгруппированнного ряда, $S_n_k -> S$ 

Рассмотрим $S_n$, найдем $k$, такое что $n_k <= n < n_(k+1)$. Пусть все члены в группе неотрицательны $S_n = S_n_k + underbrace(x_(n_k + 1), >= 0 ) + dots + underbrace(x_n, >=0) >= S_n_k$ \
$S_n = S_(n_(k + 1)) - x_(n_(k + 1)) - x_(n_k -1) - dots - x_(n+1) <= S_(n_(k+1))$

$=> S_n_k <= S_n <= S_(n_(k+1))$ если же члены в группе неположительны, то $S_(n_(k+1)) <= S_n <= S_n_k => lim S_n = S$ 
]
= Знакопостоянные ряды
В этом параграфе ряды из неотрицательных вещественных чисел

#theorem[
$x_n >= 0, forall n$ тогда $sum_(n=1)^oo x_n$ - сходится $<=>$ последовательность частичных сумм ограничена
]
#proof[
$S_(n+1) = S_n + x_(n+1) >= S_n$, то есть частисные суммы возрастают. А возрастающая последовательность имеет предел $<=>$ она ограничена
]
#theorem[Признак сравнения][
$0 <= x_n <= y_n forall n$. Тогда если $sum_(n=1)^oo y_n$ сходится, то $sum_(n=1)^oo x_n$ - сходится.
] <theorem:riznaksravn>
#proof[
$sum_(n=1)^oo y_n$ - сходится $=> overline(S)_n:= sum_(k=1)^n y_k$ - ограниченная $=> 0<= S_n = sum_(k=1)^n x_k <= overline(S)_n$ $=>$ $S_n$ - ограничена $=> sum_(n=1)^oo x_n$ - сходится
]
#corollary[Corollary of @theorem:riznaksravn][
+ Если $a_n = O(b_n)$ и ряд $sum b_n$ - сходится, то $sum a_n$ - сходитсяб $a_n, b_n >=0$
+ Если $a_n, b_n >= 0$ и $a_n ~ b_n$, то ряды $sum a_n$ и $sum b_n$ ведут себя одинаково
]
#proof[
+ $a_n = O(b_n) => 0 <= a_n <= C b_n$ но ряд $sum_(n=1)^oo C b_n$ сходится
+ $a_n ~ b_n$ означает, что $lim a_n/b_n = 1$, означает, что последовательность ограничена $=> a_n/b_n <= C => a_n = O(b_n)$, аналогично $b_n = O(a_n)$ 
]
#theorem[Признак Коши][
$a_n >= 0$. Тогда
+ Если $root(n, a_n) <= q < 1$ для достаточно больших $n$, то ряд $sum_(n=1)^oo a_n$ - сходится
+ $q_* = overline(lim) root(n, a_n)$. Если $q_* < 1$, то ряд сходится, если $q_* > 1$, то ряд расходится, более того частичные суммы ряда не стремятся к нулю
] 
#corollary[
+ Пусть $root(n, a_n)<= q < 1$ $forall n >= N$, тогда $a_n <= q^n $ при $n >= N$. Занулим члены ряда с индексами $< N$, на сходимость не влияет. Тогда $a_n <= q^n forall n$ и признка сравнения с рядом $sum_(n=1)^oo q^n$, а он сходящийся
+ $q_* > 1$ $overline(lim)$ - некоторый частичный предел $=>$ найдется $a_n_k$, такой что $root(n_k, a_n_k) -> q_* > 1$ начиная с некоторого номера $root(n_k, a_n_k) > 1 => a_n_k > 1 => a_n$ не стремится к нулю $=>$ ряд расходится \ $q_* < 1, q_* = lim root(n, a_k) = lim_(n->oo) sup_(k>=n) root(k, a_k)$, пусть $q:= (1+q_k)/2$

$=>$ Начиная с некоторого номера $abs(b_n - q_*) < epsilon = (1-q_*)/2 => b_n < q => root(n, a_n)<= b_n < q$ это пункт 1
]
#warning-block[
Если $q_* = 1$, то ряд может сходится, а может расходится, а может и не может
$sum_(n=1)^oo 1/n$ - расходится. $root(n, a_n) = 1/root(n, n) -> 1$ \
$sum_(n=1)^oo 1/(n (n+1))$ - сходится 
]
#theorem[ Даламбера (не Ламберта)][
$a_n > 0$
+ Если $(a_(n+1))/a_n <= d < 1$ начиная с некоторого номера, то ряд $sum_(n=1)^oo a_n$ сходится
+ Пусть $d_* := lim (a_(n+1))/a_n$, если $d_* < 1$, то ряд сходится, если $d_* > 1$, то ряд расходится, более того члены ряда не стремятся к нулю
]
#proof[
+ Пусть $a_(n+1)/a_n <= d$ при $n >= N => a_(n+1) <= d a_n, forall n >= N$, $a_(n+2) <= d a_(n+1) <= d^2 a_n => a_n <= d^(n-N) a_N$ при $n >= N$. \ Занулим $a_n$ при $n < N$ тогда $a_n <= C d^n forall n$, где $C = a_N/d^n$, и признак сравнения с геом. прогрессией
+ $d_* > 1 =>$ при больших $n: a_(n+1)/a_n > 1 => a_n < a_(n+1) < a_(n+2) < dots =>$ нет стремления к нулю \ $d_* < 1$, $epsilon = (1-d_*)/2$ при больших $n: abs(a_(n+1)/a_n - d_*) < epsilon = (1-d_*)/2 => a_(n+1)/a_n < d$ при больших $n$, значит попали в первый пункт
]
#note-block[
про $d_* = 1$ тоже работает
]
#exercise[
+ доказать, что $overline(lim) a_(n+1)/a_n < 1$, то сходится
+ если $underline(lim) a_(n+1)/a_n > 1$, то ряд расходится
]
#example[
$x>0$ $sum_(n=0)^oo x^n/n!$, $a_n = x^n/n!$

$a_(n+1)/a_n = (x^(n+1))/(n+1)! : x^n/n! = x/(n+1) -> 0 < 1$ ряд сходится

Коши $root(n, a_n) = root(n, x^n/n!) = x/root(n, n!) ~ x/root(n, n^n e^(-n) sqrt(2 pi n)) = x/(n e^-1 root(2n, 2 pi n)) ~ (x e)/n -> 0 < 1$
]

#theorem[
$a_n > 0$. Если существует $lim a_(n+1)/a_n =: d_*$, то $lim root(n, a_n) = d_*$
]

#proof[
$ln root(n, a_n) = (ln a_n)/n$ посчитаем такой предел по теореме Штольца
$(ln a_(n+1) - ln a_n)/((n+1) - n) = ln (a_(n+1))/a_n = ln d_*$, значит $(ln a_n)/n -> ln d_*$
]
#theorem[
$f: [m,n] -> RR$, функция неотрицательна и монотонна, тогда $abs(integral_m^n f(x) d x - sum_(k=m)^n f(k)) <= max{f(n), f(m)}$
]

#proof[
Методом картинки \ 
$sum_(k=m)^(n-1) f(k) >= integral_m^n f(x) d x >= sum_(k=m+1)^n f(k)$ \
$f(n) <= sum_(k=m)^n f(k) - integral_m^n f(x) d x <= f(m)$
]

#theorem[Интегральный признак сходимости ряда][ 
$f: [1, +oo) -> RR$ неотрицательная, убывающая. Тогда $integral_1^(+oo) f(x) d x$ и $sum_(n=1)^oo f(n)$ ведут себя одинаково
] <theorem:intsign>

#proof[
Из сходимости интала $=> $ сходимость ряда

$F(y):= integral_1^y f(x) d x$ интеграл сходится $=>$ $F$ ограниченная функция

$=> S_n := sum_(k=1)^n f(k) <= integral_1^n f(x) d x + f(1) = F(n) + f(1) - $ ограниченная последовательность

Из сходимости суммы $=>$ сходимость интеграла

ряд сходится $=> S_n := sum_(k=1)^n f(k)$ - ограниченная последовательность $=> F(n) = integral_1^n f(x) d x <= S_n$ - ограниченная послед $=> F$ - огр. функция
]
#example[

$sum_(n=1)^oo 1/n^p$ если $p <= 0$, то члены ряда не стремятся к нулю $=>$ ряд расходится

Если $p > 0$, то $f(x) = 1/x^p > 0$ и убывает $=>$ по интегральному признаку ряд $sum_(n=1)^oo 1/n^p$ и $integral_1^oo (d x)/x^p$ ведут себя одинаково

Ряд сходится $<=> p > 1$
]
#corollary[Corollary of @theorem:intsign][
Если $a_n = O(1/n^p)$ при $p> 1$, то ряд $sum_(n=1)^oo a_n$ - абсолютно схоидтся и в частности сходится
]

#proof[
$0 <= abs(a_n) <= c/n^p$ и ряд $sum_(n=1)^oo c/n^p$ - сходится
]
= Знакопеременные ряды

#theorem[Преобразование Абеля][
$A_k := a_1 + a_2 + dots + a_k$ - префиксная сумма

Тогда $sum_(k=1)^n a_k b_k = A_n b_n + sum_(k=1)^(n-1) A_k (b_k - b_(k+1))$
]
#proof[

$A_0 := 0$, тогда $a_k = A_(k) - A_(k-1)$ \
$sum_(k=1)^n a_k b_k = sum_(k=1)^n (A_k - A_(k-1)) b_k = sum_(k=1)^n A_k b_k - sum_(j=2)^n A_(j-1) b_j  | (j-1 = k) | = sum_(k=1)^n A_k b_k - sum_(k=1)^n A_k b_(k+1) = A_n b_n + sum_(k=1)^(n-1) A_k (b_k - b_(k+1))$
]
#theorem[Признак Дирихле][
Если
+ суммы $sum_(k=1)^n a_k =: A_n$ ограничены
+ $b_n$ монотонны
+ $lim b_n = 0$
Если это выполняется, то $sum_(n=1)^oo a_n b_n$ сходится
]

#proof[

$S_n := sum_(k=1)^n a_k b_k$ для этих сумм напишем преобразование Абеля

$= A_n b_n + sum_(k=1)^(n-1) A_k (b_k - b_(k+1))$
Знаем, что $A_n$ ограничены, в частности $abs(A_n) <= M$, понимаем, что $A_n b_n$ стремится к нулю, так как это ограниченная на бесконечно малую

Значит нам надо доказать, что $sum_(k=1)^(n-1) A_k (b_k - b_(k+1))$ имеет конечный предел, означает, что ряд $sum_(k=1)^oo A_k (b_k - b_(k+1))$ сходится, вместо того, чтобы доказывать, что он сходится докажем, что он абсолютно сходится

$sum_(k=1)^oo abs(A_k) abs(b_k - b_(k+1))$, можно считать, что $b_n$ монотонно убывают, тогда один модуль не нужен

$abs(A_k) abs(b_k - b_(k+1)) <= M (b_k - b_(k+1))$

$sum_(k=1)^oo abs(A_k) abs(b_k - b_(k+1)) <= M underbrace(sum_(k=1)^oo (b_k - b_(k-1)), =b_1) = B b_1$ (так как $sum_(k=1)^n (b_k - b_(k+1)) = b_1 - b_(n+1) -> b_1$), тогда все сходится 
]

#theorem[Признак Абеля][
Если
+ Ряд $sum_(k=1)^oo a_k$ - сходится
+ $b_n$ монотонны
+ $b_n$ ограничены
то ряд $sum_(k=1)^oo a_k b_k$ сходится
]
#proof[
$2+3 => b_n$ имеют конечный предел $b:= lim b_n => overline(b_n) := b_n -b$ монотонны и $lim overline(b_n) = 0$

$A_n$ имеют конечный предел $=> A_n$ ограничены

$=>$ ряд $sum_(k=1)^oo a_k overline(b_k)$ - сходится

$sum_(k=1)^oo a_k b_k = sum_(k=1)^oo a_k b + sum_(k=1)^oo a_k overline(b_k)$ - первый это $b dot sum_(k=1)^oo a_k$ - сходится, второй знаем, что сходится $qed$
]
#definition[
$a_n >= 0$ ряд $sum_(n=1)^oo (-1)^(n-1) a_n$ - знакочередующийся ряд
]

#theorem[Признак Лейбница][
Пусть $a_n >= 0$ монотонны. Тогда

$sum_(n=1)^oo (-1)^(n-1) a_n$ - схоидится $<=> lim a_n = 0$.

Более того в случае сходимости $S_(2n) <= S <= S_(2n+1)$
]

#proof[
"$==>$" необходимое условие сходимости

"$<==$" 

$S_(2n+2) = S_(2n) + underbrace(a_(2n + 1) - a_(2n+2), >= 0) >= S_(2n)$ \
$S_(2n+1) = S_(2n-1)  underbrace(- a_(2n) + a_(2n+1), <= 0) <= S_(2n-1)$ 

$S_(2n+1) = S_(2n) + a_(2n+1) >= S_(2n)$ 

То есть получились вложенные отрезки, сначала $[0, S_1] supset [S_2, S_3] supset [S_4, S_5] supset dots$, длина $[S_(2n), S_(2n+1)]$ равна $a_(2n+1) -> 0$, то есть отрезки еще и стягивающиеся. Тогда есть $s in [S_(2n), S_(2n+1)] forall n$ и $lim S_(2n) = lim S_(2n+1) = s$, то есть делаем вывод, что $s$ - сумма ряда
]

#definition[Ряд Лейбница][

$1- 1/2 + 1/3 - 1/4 + 1/5 - dots = ln 2$ сходится по признаку Лейбница

Посчитаем...

$S_(2n) = 1 - 1/2 + 1/3 - 1/4 + dots + 1/(2n-1) - 1/(2n) = (1 + 1/2 + 1/3 + 1/4 + dots + 1/(2n-1) + 1/(2n)) - 2 (1/2 + 1/4 + dots + 1/(2n))$ первая это $H_(2n)$ гармоническое число, а второе это $H_n$ гармоническое число, получаем $H_(2n) - H_n = (ln(2n) + gamma + o(1)) - (ln(n) + gamma + o(1)) = ln(2) + o(1)$
]
#example[
$1- 1/2 - 1/4 + 1/3 - 1/6 - 1/8 + dots + 1/(2n-1) - 1/(4n-2) - 1/(4n)$

Сгруппируем по 3 $1/(2n-1) - 1/(4n-2) - 1/(4n) = 1/(4n-2) - 1/(4n) = 1/2(1/(2n-1) - 1/(2n))$

$overline(S)_(3n) = 1/2 (1 - 1/2 + 1/3 - 1/4 + dots + 1/(2n-1) - 1/(2n)) = S_(2n)/2 -> (ln 2)/2$
]
#definition[
$phi: NN -> NN$ биекция $sum_(n=1)^oo a_(phi(n))$ - перестановка ряда $sum_(n=1)^oo a_n$
]
#theorem[
+ Если $a_n >=0$ и $phi$ - перестановка, то $sum_(n=1)^oo a_(phi(n)) = sum_(n=1)^oo a_n$ в частности они сходятся и расходятся одновременно 
+ Если ряд абсолютно сходится, то $sum_(n=1)^oo a_(phi(n)) = sum_(n=1)^oo a_n$
]
#proof[
1. 
$S_n$ - частисная сумма исходного, $overline(S_n)$ - частичная сумма перестановки
$overline(S_n) = a_(phi(1)) + a_(phi(2)) + dots + a_(phi(n)) <= S_max{phi(1), phi(2), dots, phi(n)} <= S$ - сумма исходного ряда 
$overline(S_n) <= S => overline(S) := lim overline(S_n) <= S$, то есть перестановка не увеличивает сумму ряда, а тогда сумма вообще не меняется

Но обратная перестановка тоже не увеличивает сумму ряда, тогда получается, что сумма ряда просто не меняется

2.
$x_+ := max {x, 0}, x_- := max{-x, 0}$, тогда $x = x_+ - x_-, abs(x) = x_+ + x_- => 0 <= x_(plus.minus) <= abs(x)$

$sum_(n=1)^oo abs(a_n)$ - сходится $=> sum_(n=1)^oo (a_n)_plus.minus$ сходится

$0 <= (a_n)_plus.minus <= abs(a_n)$

$=> sum_(n=1)^oo (a_phi(n))_plus.minus$ сходится к тем же суммам

$sum_(n=1)^oo a_(phi(n)) = sum (a_phi(n))_+ - sum (a_phi(n))_- = sum (a_n)_+ - sum (a_n)_- = sum_(n=1)^oo a_n$
]
#definition[
Ряд сходится условно, если он сходится, но не абсолютно
]
#note-block[
Если $sum_(n=1)^oo a_n$ - сходится условно, то $sum_(n=1)^oo (a_n)_plus.minus = +oo$ 

Пусть $sum_(n=1)^oo (a_n)_plus.minus$ - конечны $=> sum abs(a_n) = sum (a_n)_+ + sum (a_n)_-$ - конечна, а такого быть не должно \

Пусть ровно одна из $sum (a_n)_(plus.minus)$ конечна $=> sum (a_n)_- = sum (a_n)_+ - sum a_n$ - оба сходится, а значит и третий сходятся и проблема 
]
#theorem[Теорема Римана о рядах][ 

Если ряд $sum a_n$ сходится условно, $s in overline(RR)$, то существует такая перестановка $phi$, что $sum a_(phi(n)) = s$. Также существует перестановка для которой ряд $sum a_(phi(n))$ расходится
]

#proof[
$(a_1)_+, (a_2)_+, dots$, выкинем нули, соответствующие отрицательным числам, а нули, соответствующие нулям мы оставим (Что?). То, что осталось - последовательность $b_1, b_2, b_3, dots$ \
$(a_1)_-, (a_2)_-, dots$ - выкинем нули, то, что осталось - последовательность $c_1, c_2, c_3, dots$.

Знаем, что $sum_(n=1)^oo b_n = sum_(n=1)^oo c_n = + oo$

случай $s in RR$. Берем $b$-шки, пока сумма не перевалит через $s$, 

$b_1 + b_2 + dots + b_(n_1-1) <= s < b_1 + b_2 + dots + b_n_1$

Далее берем $c$-шки, пока сумма не станет меньше $s$

$b_1 + b_2 + dots + b_(n_1) - c_1 - c_2 - dots - c_m_1 < s <= b_1 + dots + b_n_1 - c_1 - dots - c_(m_1 - 1)$ 

Берем $b$-шки, пока сумма не станет $>= s$ 

$b_1 + dots + b_n_1 - c_1 - dots - c_m_1 + b_(n_1 + 1) + dots + b_(n_2 - 1) <= s < b_1 + dots b_n_1 - c_1 - dots - c_m_1 + b_(n_1 + 1) + dots + b_n_2$

Дальше берем $c$-шки, пока сумма не станет $< s$, то есть $b_1 + dots + b_n_1 - c_1 - dots - c_m_1 + b_(n_1 +1) + dots + b_n_2 - c_(m_1 + 1) - dots - c_m_2 < s <= b_1 + dots + b_n_1 - c_1 - dots- c_(m_1) + b_(n_1 + 1) + dots + b_n_2 - c_(m_1 + 1) - dots - c_(m_2 + 1)$

Получим перестановку. Почему сумма будет $s$?

Делаем группы одного знака и смотрим на частичные суммы $overline(s)_1, overline(s)_2, dots $ - частичные суммы по группам

Тогда $overline(s)_(2k) < s <= overline(s)_(2k) + c_m_k$, но $c_m_k$ стремится к нулю. Получаем, что $ s- c_m_k <=overline(s)_(2k) < s$ 

$overline(s)_(2k-1) > s >= overline(s)_(2k-1) - b_n_k, s < overline(s)_(2k-1) <= s + b_n_k => lim overline(s)_k = s, $ получаем, что ряд сходится

случай $s=+oo$

Берем $b$-шки, пока не перевалим за 1 $b_1 + dots + b_(n_1 - 1) <= 1 < b_1 + b_2 + dots + b_n_1$ затем одну $c$-шку.

Берем $b$-шки пока не перевалим через 2

$b_1 + dots + b_n_1 - c_1 + b_(n_1 + 1) + dots + b_(n_2 - 1) <= 2 < b_1 + dots + b_n_1 - c_1 + b_(n_1 + 1) + dots + b_n_2$ и так далее

Случай раcходимости

Берем $b$-шки, пока не перевалим через $1$, берем $c$-шки, пока не перевалим через $-1$, берем $b$-шки пока не перевалим через $1$ и так далее
]
#theorem[Теорема Коши про произведение рядов][

Пусть ряды $sum_(n=1)^oo a_n =: A$ и $sum_(n=1)^oo b_n =: B$ абсолютно сходятся

Тогда ряд, составляленный из произведений $a_j b_k$ в любом порядке абсолютно сходится и его сумма равна $A B$
]
#proof[
$A_n := sum_(k=1)^n a_k, A_n^*:= sum_(k=1)^n abs(a_k)$ и $A^*:= sum_(k=1)^oo abs(a_k)$ аналогично с $B$

Рассмотрим ряд, составленный из $abs(a_j b_k)$ $S_n$ - его частичные суммы

Нужно проверить, что $S_n$ ограничены сверху. Докажем, что $S_n <= A^* B^*$ \

$S_n <= (abs(a_1) + abs(a_2) + dots + abs(a_j)) ( abs(b_1) + abs(b_2) + dots + abs(b_k)) = A_j^* B_k^* <= A^* B^*$, где $j$ - наиб из индексов $j$, встречающийся в сумме $S_n$. $k$ - наибольший из индексов $k$, встречающийся в сумме $S_n$

$=>$ ряд из $a_j b_k$ абсолютно сходится $=>$ можно переставлять слагаемые не меняя суммы

$a_1 b_1, a_1 b_2, a_1 b_3, a_1 b_4, dots$

$a_2 b_1, a_2, b_2, dots$

$a_3 b_1, a_3 b_2, dots$

$dots,$

Пусть $S_n$ - частичная сумма такой перестановки ряда

Рассмотрим $S_(n^2)$ - должны сложить всю такую табличку $n times n$, поэтому $S_(n^2) = (a_1 + a_2 + dots + a_n) (b_1 + b_2 + dots + b_n) = A_n B_n -> A B$
]
#definition[
Произведение рядов $sum_(n=1)^oo a_n$ и $sum_(n=1)^oo b_n$ - это ряд $sum_(n=1)^oo c_n$, где $c_n = a_1 b_n + a_2 b_(n-1) + a_3 b_(n-2) + dots + a_n b_1$ (то есть берем в этой табличке суммы по диагонали) 

Мотивировка. $(a_1 t + a_2 t^2 + dots a_n t^n) ( b_1 t + b_2 t^2 + dots b_n t^2) = a_1 b_1 t^2 + (a_1 b_2 + a_2 b_1) t^3 + (a_1 b_3 + a_2 b_2 + a_3 b_1) t^4 + dots$
]
#theorem[ Теорема Мертенса][

Если ряды $sum a_n$ и $sum b_n$ сходится, при чем один из них абсолютно, то произведение рядов сходится и его сумма равна произведению $sum a_n dot sum b_n$
]
#proof[
Вообще пофигу на него, какое-то там глиномесиво, которое никому нахрен не вперлось
]
#warning-block[
Если вообще нет абсолютной сходимости, то произведение рядов может быть расходящися рядом
]
#example[
$sum_(n=1)^oo (-1)^(n-1)/(sqrt(n))$ - сходится по принциау Лейбница

$a_n = b_n = (-1)^(n-1)/sqrt(n)$, $c_n = a_1 b_n + a_2 b_(n-2) + dots + a_n b_1 = (-1)^n (1/(sqrt(1) sqrt(n)) + 1/(sqrt(2) sqrt(n-1)) + dots + 1/(sqrt(n) sqrt(1)))$ \

$1/(sqrt(k) sqrt(n-k+1)) >= 2/(n+1)$ \
$sqrt(k) sqrt(n-k+1) <= (k + (n-k + 1))/2 = (n+1)/2$ 

$=> abs(c_n) >= (2n)/(n+1) >= 1 => c_n$ не стремится к 0 и ряд расходится
]
#lemma[
$lim x_n = x in RR, lim y_n = y in RR$ Тогда $lim (x_1 y_n + x_2 y_(n-1) + dots + x_n y_1)/n = x y$ й
]
#proof[
Случай $y = 0$, $x_n$ - ограниченная $=> abs(x_n) <= M$ \

$abs( (x_1 y_n + x_2 y_(n-1) + dots + x_n y_1)/(n) ) <= (abs(x_1) abs(y_n) + abs(x_2) abs(y_(n-1)) + dots + abs(x_n) abs(y_1))/n <= M dot (abs(y_1) + abs(y_2) + dots + abs(y_n))/n$ - стремится к 0 по Штольцу

$y_n = y forall n$

$(x_1 y_n + x_y y_(n-1) + dots + x_n y_n)/(n) = y dot (x_1 + x_2 + dots + x_n)/2 -> x y$ по Штольцу

Общий случай $overline(y)_n = y_n - y -> 0$ \

$(x_1 y_n + x_2 y_(n-1) + dots + x_n y_1)/n = (x_1 overline(y)_n + x_2 overline(y)_(n-1) + dots + x_n overline(y)_1)/n + (x_1 y + x_2 y + dots + x_n y)/n = x y$
]
#theorem[Теорема Абеля о произведении рядов][

$sum_(n=1)^oo a_n =: A, sum_(n=1)^oo b_n =: B$ и $sum_(n=1)^oo c_n =: C$ все ряды сходятся и $sum x_n$ - произведение рядов, то есть $c_n = a_1 b_n + a_2 b_(n-1) + dots + a_n b_1$ Тогда $A B = C$
]
#proof[

$A_n := sum_(k=1)^n a_k, B_n = sum_(k=1)^n b_k, C_n := sum_(k=1)^n c_k$

Расссмотрим $(A_1 B_n + A_2 B_(n-1) + dots + A_n B_1)/n -> A B$ (по лемме)

С другой стороны раскроем скобки $1/n ( n underbrace(a_1 b_1, C_1) + (n-1) underbrace((a_1 b_2 + a_2 b_1), C_2) + (n-2) underbrace((a_1 b_3 + a_2 b_2 +  a_3 b_1), C_3) + dots + underbrace((a_1 b_n + a_2 b_(n-1) + dots + a_n b_1), C_n)) = (C_1 + C_2 + dots + C_n)/n -> C$
]
= Бесконечные произведения

#definition[
$product_(k=1)^oo x_k$ - бесконечное произведение, $x_k != 0 forall k$

$P_n := product_(k=1)^n x_k$ - частичное прозвиеденеие

Если существуеют $lim_(n->oo) P_n$, то он называется значением бесконечного произведения

Бесконечное произведение называется сходящимся, если $lim_(n-> oo) P_n$ если этот предел конечный и ненулевой
]
#example[
$product_(k=2)^oo (1-1/k^2)$

$P_n = (1-1/2^2) (1-1/3^2) + dots (1-1/n^2) = (1 dot 3 dot 2 dot 4 dot 3 dot 5 dots (n-2)n dot (n-1) dot (n+1))/(2^2 3^2 dots n^2) = (n+1)/(2n) -> 1/2$ 
]
#example[

$product_(k=1)^oo (1-1/(4k^2))$

$P_n = (1-1/4) (1-1/4^2) (1-1/6^2) dots (1-1/(2n)^2) = (1 dot 3 dot 3 dot 5 dot 5 dot 7 dots dot (2n-1)(2n+1))/(2^2 4^2 6^2 dots (2n)^2) = ((2n-1)!!)^2/((2n)!!)^2 dot (2n+1) -> 2/pi$ (формула Валлиса)
]

#exercise[
+ $product_(k=1)^oo (1-1/(2k+1)^2) = pi/4$
+ $product_(k=1)^oo (1+x^2^(k-1)) = 1/(1-x)$
]
#property[

+ Изменение конечного числа сомножителей (на ненулевые числа) не влияет на сходимость
+ Если $product_(k=1)^oo x_k$ - сходится, то $lim x_n = 1$ \ Доказательство: \ $lim x_n = lim (P_n)/(P_(n-1)) = (lim P_n)/(lim P_(n-1)) = P/P = 1$
+ У сходящегося бесконечного произведения все сомножители начиная с некоторого номера положительны
+ Пусть $x_n > 0 forall n$, тогда $product_(k=1)^oo x_k$ - сходится $<=> sum_(k=1)^oo ln x_k$ - сходится и в этом случае значение произведения $product_(k=1)^oo x_k = exp(sum_(k=1)^oo ln x_k)$
]
#proof[

$S_n := sum_(k=1)^n ln x_k = ln P_n -> ln P$

$S_n -> S := sum_(k=1)^oo ln x_k$ 

$P != 0$ и $+ oo <=> S != plus.minus oo$
]
#example[
$p_n$ - $n$-ое простое число

$product_(k=1)^oo p_k/(p_k - 1) = product_(k=1)^oo 1/(1-1/p_k) = product_(k=1)^oo sum_(n=1)^oo 1/p_k^n = sum 1/(p_1^alpha_1 p_2^alpha_2 dots p_n^alpha_n) = sum_(n=1)^oo 1/n = + oo$

$1/(1-1/p_k) = sum_(n=1)^oo 1/(p_k^n)$

(слишком нагло провернулия, формализуем)

Рассмотрим $P_n = product_(k=1)^n sum_(j=1)^oo 1/p_k^j >= product_(k=1)^n sum_(j=1)^n 1/p_k^j = sum 1/(p_1^alpha_1 p_2^alpha_2 dots p_n^alpha_n), alpha_1, alpha_2, dots, alpha_n in {0,1,dots, n} $

$sum 1/(p_1^alpha_1 p_2^alpha_2 dots p_n^alpha_n) >= sum_(k=1)^n 1/k$
]

#note-block[

$product_(k=1)^n (p_k)/(p_k-1) >= H_n := sum_(k=1)^n 1/k$
]
#theorem[

Пусть $p_n$ - $n$-ое простое число. Ряд $sum_(n=1)^oo 1/p_n$ - расходится
]
#proof[

$ln(1/(1-1/p_k)) = - ln (1 - 1/p_k)$

$ln (1-x) <= x + x^2$ при $x in [0, 1/2]$

$= - ln(1-1/p_k) = 1/p_k + 1/p_k^2  => ln H_n <= sum_(k=1)^n ln(1/(1-p_k)) <= sum_(k=1)^n (1/p_k + 1/p_k^2) <= sum_(k=1)^n 1/p_k + underbrace(sum_(k=1)^oo 1/p_k^2 < 2)$

Получилось $sum_(k=1)^n 1/p_k >= ln H_n - 2 -> +oo$

$f(x) = x + x^2 + ln(1-x), f(0) = 0, f`(x) = 1 + 2x + 1/(1-x) = ((1+2x)(1-x)-1)/(1-x) = (x - 2x^2)/(1-x) >= 0$ на $[0,1/2]$
]

#note-block[
$sum_(k=1)^n 1/p_k >= ln H_n >= ln ln n$

$H_n = ln n + gamma + o(1)$ 
На самом деле $sum_(k=1)^n 1/p_k = ln ln n + O(1)$
]
#exercise[
+ $sum_(k<=p<k^2) 1/p < 4/3$
+ из предыдущего вывести $sum_(p<=n) 1/p < 2 ln ln n + 4$
]
= Функциональные последовательности и ряды

#definition[
$f, f_n: E -> RR$ последователность функция $f_n$ поточечно сходится к функции $f$, если $forall x in E:  lim_(n->oo) f_n (x) - f(x)$
]
#definition[
$f, f_n: E -> RR$ последовательность функция $f_n$ равномерно на $E$ сходится к функции $f$, если $forall epsilon > 0: exists N; forall n >= N: forall x in E => abs(f_n (x) - f(x)) < epsilon$

обозначается $f_n arrows.rr f$
]
#example[
$f_n (x) = x^n$ на $(0,1)$
$f_n$ поточечно сходится $f(x) equiv 0$

А равномерной сходимости нет 
]


#theorem[
$f_n, f: E -> RR$ Тогда 

$f_n arrows.rr f$ на $E <=> a_n:= sup_(x in E) abs(f_n (x) - f(x)) ->_(n->oo) 0$
]
#proof[
"$<==$"

$forall epsilon > 0: exists N forall n >= N: forall x in E abs(f_n (x) - f(x)) < epsilon => sup_(x in E) abs(f_n (x) - f(x)) <= epsilon$

$=> forall epsilon > 0: exists N: forall n >= N: abs(a_n) <= epsilon => a_n -> 0$

"$==>$"

$a_n -> 0 => forall epsilon > 0 exists N: forall n >= N: a_n < epsilon, abs(f_n (x) - f(x)) <= a_n$

$forall epsilon > 0: exists N: forall n >= N: forall x in E: abs(f_n (x)- f(x)) < epsilon$
]
#corollary[
$f_n ,f: E -> RR$ Если $forall x in E$ $abs(f_n(x) - f(x)) <= c_n$ и $lim c_n = 0$, то $f_n arrows.rr_("на" E) f$ \ Доказывать нечего: из неравенства на $c_n$ следует $a_n <= c_n => lim a_n = 0$
]
#corollary[
$f_n arrows.rr f$ на $E$ $<=>$ для любой последовательности $x_n in E: lim_(n->oo) (f_n (x_n) - f(x_n)) = 0$
]
#proof[

"$==>$" $abs(f_n (x_n) - f(x_n)) <= a_n => ...$ очев

"$<==$" $a_n = sup_(x in E) abs(f_n (x) - f(x))$ найдется такой $x_n in E$, что $abs(f_n (x_n) - f(x_n)) > a_n/2$ $=> lim abs(f_n (x_n) - f(x_n)) = 0 => lim a_n = 0$
]

#definition[
$f_n: E -> RR$ - равномерно ограниченная последовательность, если существует $M in RR$, такая что $abs(f_n (x)) <= M$ и $forall x in E forall n$
]
#theorem[
$f_n, g_n: E -> RR$, $f_n$ равномерно ограничена, $g_n arrows.rr 0$. Тогда $f_n g_n arrows.rr 0$
]

#proof[
$abs(f_n (x) g_n (x)) <= M abs(g_n (x))$

$sup abs(f_n (x) g_n (x)) <= M sup abs(g_n (x)) -> 0$
]

#text(fill: white)[
  Гестаповцы облажили все выходы, но Штирлиц не растерялся и вышел через вход


  Парам-пам-пам, парам-пам-пам, парам   пам    пам
]

#theorem[Критерий Коши][
$f_n: E -> RR$ Тогда $f_n$ равномерно сходится к некоторой функции $<=> forall epsilon > 0: exists N: forall m,n >= N, forall x in E => abs(f_n (x) - f_m (x)) < epsilon$
]
#proof[
"$==>$" Пусть $f_n arrows.rr f$ на $E$. Возьмем $epsilon > 0$

$exists N: forall n >= N: forall x in E: abs(f_n (x) - f(x)) < epsilon/2$

$forall m >= N: exists x in E: abs(f_m (x) - f(x)) < epsilon/2$

$=> abs(f_n (x) - f_m (x)) <= abs(f_n (x) - f(x)) + abs(f (x) - f_m (x)) < epsilon/2 + epsilon/2 = epsilon$

"$<==$"

Зафиксируем $x in E$. Тогда числовая последовательность $f_n (x)$ - фундаментальна
$=> $ у нее есть конечный предел $f(x) := lim f_n (x)$. проверим, что $exists N: forall m > n >= N: forall x in E: abs(f_n (x) - f_m (x)) < epsilon$

Устремим $m$ к бесконечности, $abs(f_m (x) - f(x)) <= epsilon$
]
#definition[
Пространство $l^oo (E) := {f: E -> RR | f - "огр. функция"}$ 

$norm(f)_(l^oo (E)) = norm(f)_oo := sup_(x in E) abs(f(x))$ - норма
]
#definition[
Пространство $C(K)$. $K$ - компакт, $C (K) := {f : K -> RR | f - "непрерывна"}$

$norm(f)_(C(K)) = norm(f)_oo := max_(x in K) abs(f(x))$
]
#note[
$C(K) subset  l^oo (K)$
]
#note[
$f_n arrows.rr f$  на $E$ $<=> norm(f_n - f)_oo ->_(n->oo) 0$
]
#theorem[

$l^oo (E)$ - полное пространство
]
#proof[
Пусть $f_n$ - фундаментальная последовательсность в $l^oo (E)$, это значит, что $forall epsilon > 0: exists N: forall m, n >= N: norm(f_n - f_m) < epsilon$, $norm(f_n - f_m) = sup_(x in E) (f_n (x) - f_m (x))$

$=> forall epsilon > 0: exists N : forall m,n >= N: forall x in E: abs(f_n (x) - f_m (x)) < epsilon$ это условие из критерия Коши. 

Найдется $f: E -> RR$, для которой $f_n arrows.rr f$ на $E$, то есть $sup_(x in E) abs(f_n (x) - f(x)) -> 0 => norm(f_n - f)_oo -> 0$

Осталось проверить, что $f in l^oo (E)$

Возьмем такое $n$, что $forall x in E: abs(f_n (x) - f(x)) < 1$

$abs(f(x)) <= abs(f_n (x)) + abs(f(x) - f_n (x)) < 1 + abs(f_n (x)) <= 1 + norm(f_n)_oo$

Следовательно $f$ ограниченная функция
]
#theorem[

$f, f_n : E -> RR, a in E$ $f_n$ непрерывна в точке $a$ и $f_n arrows.rr f$ на $E$

Тогда $f$ непрерывна в точке $a$
]
#proof[
Если $a$ не предельная точка, то все очевидно. Считаем, что предельная

Возьмем $epsilon > 0$. По нему $N$, такой что $forall n >= N: forall x in E: abs(f_n (x) - f(x)) < epsilon$

Рассмотрим функцию $f_N$ она непрерывна в точке $a => exists delta > 0: forall x in E$, такой что $abs(x-a) < delta => abs(f_N (x) - f_N (a)) < epsilon$

Возьмем $x in E$, такой что $abs(x-a) < delta$

$abs(f(x) - f(a)) <= underbrace(abs(f(x) - f_N (x)), < epsilon  "по выбору" N) + underbrace(abs(f_N (x) - f_N (a)), < epsilon "по выбору" delta) + underbrace(abs(f_N (a) - f(a)), < epsilon "по выбору" N) < 3 epsilon$
]
#corollary[Теорема Стокса-Зайделя][ 

$f_n, f: E ->RR, f_n$ - непрерывная во всех точках $forall n$
и $f_n arrows.rr f$. Тогда $f$ непрерывна во всех точках
]
#corollary[
$C(K)$ - полное пространство
]
#proof[
$C(K)$ - замкнутое подпространство $l^oo (K)$
]
#definition[

$sum_(k=1)^oo u_k (x), u_k: E -> RR$

Ряд сходится поточечно на $E$, если $forall x in E$ числовой ряд $sum_(k=1)^oo u_k (x)$ - сходящийся

Ряд сходится равномерно на $E$, если $S_n (x):= sum_(k=1)^n u_k (x)$ равномерно сходится $$
]

#definition[

Пусть ряд $sum_(k=1)^oo u_k (x)$ поточечно сходится

Остаток ряда $r_n (x):= sum_(k=n+1)^oo u_k (x)$
]
#theorem[
$sum_(k=1)^oo u_k$ равномерно сходятся $<=> r_k arrows.rr 0$
]
#proof[
Ряд равномерно сходится $<=> S_n$ равномерно сходится, то есть равномерно сходится к $S(x):= sum_(k=1)^oo u_k (x) <=> underbrace(S - S_n, = r_n) arrows.rr 0$
]
#corollary[необходимые условие равносильности сходимости ряда][
$sum_(n=1)^oo u_n (x)$ равномерно сходятся на $E$

$-> u_n arrows.rr 0$ на $E$
]
#proof[
$S_n := sum_(k=1)^n u_k arrows.rr S := sum_(k=1)^oo u_k => u_n = S_n - S_(n-1) arrows.rr S - S = 0$
]
#note[
+ Если существуеют такие $x_n in EE$, что $abs(u_n (x_n)) > epsilon$, то равномерной сходимости нет (так как в этом случае $u_n !arrows.rr 0$)

+ Если существуют $x_n in E$ для которых $sum_(n=1)^oo u_n (x_n)$ расходится, то из этого не следует отсутсвие равномерной сходимости ряда $u_n (x) = cases(1/n "при" x in (1/(n+1); 1/n], 0 "иначе")$ $sum u_n (1/n) = sum 1/n$ - расходится. Но ряд $sum u_n$ равносерно сходится на $[0,1]$
]
#theorem[Критерий Коши для равномерной сходимости ряд][
$u_n: E -> RR$ тогда ряд $sum_(k=1)^oo u_n (x)$ равномерно сходится на $E <=> forall epsilon > 0 exists N: forall n > m >= m: forall x in E => abs(sum_(k=m+1)^n u_k (x)) < epsilon$
]
#proof[
$S_n := sum_(k=1)^n u_k$

$sum_(k=1)^oo u_k$ сходится равномерно $<=> S_n$ сходится равномерно $<==>^"крит. Коши"$ $forall epsilon > 0 exists N : forall n > m >= N: forall x in E => abs(S_n (x) - S_m (x)) < epsilon, S_n (x) - s_m (x) = sum_(k=m+1)^n u_k (x)$
]
#theorem[Признак сравнение][
$u_N, v_n : E -> RR, abs(u_n (x)) <= v_n (x) forall n forall x in E$

$sum_(n=1)^oo v_n (x)$ равномерно сходится на $E$. Тогда $sum_(n=1)^oo u_n (x)$ равномерно сходится на $E$
]
#proof[
$sum_(n=1)^oo v_n$ равномерно сходится $<==>^"кр. Коши"$ $forall epsilon > 0: exists N: forall n > m >= N: forall x in E => abs(sum_(k=m+1)^oo v_n (x)) < epsilon, abs(sum_(k=m+1)^n u_k (x)) <= sum_(k=m+1)^n abs(u_k (x)) <= abs(sum_(k=m+1)^n v_n)$

$=>$ критерий Коши для $sum_(n=1)^oo u_n (x)$
]
#corollary[
+ Если ряд $sum_(n=1)^oo abs(u_n (x))$ равномерно сходится на $E$, то $sum_(n=1)^oo u_n (x)$ равномерно сходится на $E$. \ Доказательстов: $v_n (x) := abs(u_n (x))$

+ Если $abs(u_n (x)) <= a_n in RR forall x in E$, и ряд $sum_(n=1)^oo a_n$ - сходится, то $sum_(n=1)^oo u_n (x)$ сходится равномерно на $E$ (признак Вейерштрасса) \ Доказательство: $v_n (x) equiv a_n$
]
#warning-block[
Равномерная и абсолютная сходимость про разное

+ $sum_(n=1)^oo x^n, x in (0,1)$ абсолютно сходится, а равномерно нет #emoji.face.sad $x^n !arrows.rr 0$

+ $sum_(n=1)^oo (-1)^n/n$ равномерно сходимость нет, а абсолютной нет
+ Бвают ряды $sum_(n=1)^oo u_n (x)$ схоидтся равномерно, сходится абсолютно, но ряд $sum_(n=1)^oo abs(u_n (x))$ сходится равномерно
]
#theorem[Признак Дирихле][
$a_n, b_n : E -> RR$. Если
+ частичные суммы $sum_(k=1)^n a_k (x) =: A_n (x)$ равномерно ограничены
+ $b_n arrows.rr 0$ на $E$
+ $b_n (x)$ монотонные по $n forall x in E$
То ряд $sum_(n=1)^oo a_n (x) b_n (x)$ сходится равномерно на $E$
]
#proof[
$A_n := sum_(k=1)^n a_k$. Надо доказать, что $S_n := sum_(k=1)^n a_k b_k$ равномерно сходится

$S_n = A_n b_n + sum_(k=1)^(n-1) A_k (b_k - b_(k+1))$

$A_n b_n arrows.rr 0$ так как равномерно ограниченная на равномерно стремящуюся к 0

Осталось доказать, что ряд $sum_(k=1)^n A_k (b_k - b_(k+1))$ равномерно сходящийся

По признак сравнения достаточно доказать, что $sum_(k=1)^oo M abs(b_k - b_(k+1))$ равномерно сходится, где $abs(A_k (x)) <= M forall k forall x$

то есть что $sum_(k=1)^oo abs(b_k - b_(k+1))$ равномерно сходится

то есть, что $sum_(k=1)^n abs(b_k - b_(k+1))$ равномерно сходится, то есть получается, что $sum_(k=1)^n abs(b_k - b_(k+1)) = abs(sum_(k=1)^n (b_k - b_(k+1))) = abs(b_1 - b_(n+1)) arrows.rr abs(b_1)$
]
#theorem[Признак Абеля][

$a_n ,b_n: E -> RR$. Если 
+ ряд $sum_(k=1)^oo a_k (x)$ равномерно сходящийся на $E$
+ $b_n$ равномерно ограничены
+ $b_n (x)$ монотонные по $n forall x in E$
То $sum_(n=1)^oo a_n (x) b_n (x)$ равномерно сходится на $E$
]
#proof[
$A_n := sum_(k=1)^n a_k, A:= sum_(k=1)^oo a_k, alpha_n := A - A_n = sum_(k=m+1)^oo a_k arrows.rr 0$ (так как хвосты равномерно сходящегося ряда)

Доказать нужно что $S_n$ равномерно сходится ($S_n$ такой же, как и был)

$S_n = underbrace(A_n b_n, A - alpha_n) + sum_(k=1)^(n-1) underbrace(A_k, A - alpha_k) (b_k - b_(k+1)) = A dot b_n - alpha_n b_n + underbrace(sum_(k=1)^(n-1) A (b_k - b_(k+1)), A b_1 - A b_n) - sum_(k=1)^(n-1) alpha_k (b_k - b_(k+1))$
Осталось доказать, что $alpha_n b_n + sum_(k=1)^(n-1) alpha_k (b_k - b_(k+1))$ равномерно сходится

$alpha_n b_n arrows.rr 0$ равномерно стрем. к 0 на равномерно ограниченную

Осталось понять, что $sum_(k=1)^oo alpha_k (b_k - b_(k+1))$ равномерно сходящийся ряд

Применим условие критерия Коши $abs(b_n) <= M$

Зафиксируем $epsilon > 0$, найдется такой номер $N$, такой что $forall n >= N: forall x in E: abs(alpha_n (x)) < epsilon$

При $n > m >= N$

$abs(sum_(k=m+1)^n alpha_k (b_k - b_(k+1))) <= sum_(k=m+1)^n underbrace(abs(alpha_k), < epsilon) abs(b_k - b_(k+1)) < epsilon dot sum_(k=m+1)^n abs(b_k - b_(k+1)) = epsilon abs(sum_(k=m+1)^n (b_k - b_(k+1))) = epsilon abs(b_(m+1) - b_(n+1)) <= epsilon (abs(b_(m+1)) + abs(b_(n+1))) <= 2 M epsilon$

И тогда получаем, что $sum_(k=1)^oo alpha_k (b_k - b_(k+1))$ равномерно сходится
]

#theorem[Признак Лейбница][
$b_n (x) >= 0 forall n forall x in E$ и $b_n arrows.rr$ на $E$, $b_n$ монотонны по $n forall x in E$

Тогда $sum_(n=1)^oo (-1)^n b_n (x)$ равномерно сходится на $E$
]
#proof[
  
  $a_n = (-1)^(n-1)$ и признак Дирихле
]
#example[

$x in (0,1)$

ряд $sum_(n=1)^oo ((-1)^(n-1) x^n)/n$ равномерно сходится по признаку Лейбника $b_n (x) = x^n/n$

$b_n$ монотонно убывают и $b_n arrows.rr 0$, так как $abs( b_n (x)) <= 1/n -> 0$

Ряд $(*)$ абсолютно сходится, так как $sum_(n=1)^oo x^n/n$ сходится (например по признаку Даламбера), но ряд из модулей уже не сходится равномерно

$sum_(k=1)^oo abs(((-1)^(n-1) x^n)/n) = sum_(n=1)^oo x^n/n$ не сходится равномерно

Критерий Коши. Пусть сходится равномерно, тогда $forall epsilon > 0: exists N: forall n > m >= N: forall x in (0,1)$

$sum_(k=m+1)^n x^k/k < epsilon$ устремим $x -> 1$, $sum_(k=m+1)^n 1/k <= epsilon$, это не так, $sum_(k=m+1)^(2m) 1/k > 1/2$, то есть получаем противоречие
]
= Свойства равномерно сходящихся последовательностей и рядов

#theorem[
$f_n ,f : E -> RR$, $a$ - предельная точка $E$, $f_n arrows.rr f$ на $E$. $b_n := lim_(x->a) f_n (x) in RR$. Тогда $lim_(n->oo) b_n$ и $lim_(x-> a) f(x)$ существуют, конечны и равны. То есть получается, что $lim_(n->oo) lim_(x->a) f_n (x) = lim_(x-> a) lim_(n-> oo) f_n (x)$
]
#proof[
$f_n arrows.rr f$ на $E$ $==>^"кр. Коши"$ $forall epsilon > 0 exists N: forall n > m >= N: forall x in E$ $abs(f_m (x) - f_n (x)) < epsilon$, $x-> a: f_m (x) -> b_m, x->a: f_n (x) -> b_n$
$=> forall epsilon > 0: exists N: forall m,n >= N: abs(b_m - b_n) <= epsilon$

$==>^"Кр. Коши"$ $b_n$ имеет конечный предел, $b:= lim_(n->oo) b_n$

Докажем, что $lim_(x->a) f(x) = b$

$abs( f(x) - b) <= underbrace(abs(f(x) - f_n (x)), < epsilon "при" forall x in E "и" n >= N_1) + abs( f_n (x) - b_n) + underbrace(abs(b_n - b), < epsilon "при" n >= N_2) < 2 epsilon + underbrace(abs(f_n (x) - f(x)), <epsilon "при" abs(x-a) < delta)$ можем выбрать такой $delta$, то есть вся эта херабора $< 3 epsilon$

$=> lim_(x->a) f(x) = b$
]
#theorem[

$u_k: E -> RR, a$ - предельная точка $E$, $c_n := lim_(x->a) u_n (x) in RR, sum_(n=1)^oo u_n (x)$ равномерно сходится на $E$

Тогда $lim_(x->a) sum_(n=1)^oo u_n (x) = sum_(n=1)^oo c_n = sum_(n=1)^oo lim_(x->a) u_n (x)$
]
#proof[
$f_n := sum_(k=1)^n u_k arrows.rr f:= sum_(k=1)^oo u_k, b_n = lim_(x->a) f_n (x) = lim_(x->a) sum_(k=1)^n u_k (x) = sum_(k=1)^n lim_(x->a) u_k (x) = sum_(k=1)^n c_k$

Тогда по теореме $sum_(k=1)^oo c_k = lim_(n->oo) b_n = lim_(x->a) f(x) = lim_(x->a) sum_(k=1)^oo u_k (x)$
]
#corollary[

$f_n ,f: E -> RR, a in E, f_n arrows.rr f$ на $E$ и $f_n$ непрерывна в точке $a => f$ непрерывна в точке $a$
]
#proof[

Если $a$ не предельная точка $E$, то нечего доказывать. Если $a$ - предельная точка $E$, то $f_n (a) = b_n = lim_(x->a) f_n (x) => f(a) = lim_(n->oo) f_n (a) = lim b_n = lim_(x->a) f (x) => f$ неперывная в точка $a$
]
#corollary[
Аналогично про ряд: 

$u_n : E -> RR, a in E, sum_(n=1)^oo u_n (x)$ равномерно сходится, $u_n$ неперывна в точке $a$

Тогда $sum_(n=1)^oo u_n (x)$ непрерывна в точке $a$
]
#proof[

$c_n = lim_(x-> a) u_n (x) = u_n (a) => sum_(n=1)^oo u_n (a) = sum_(n=1)^oo c_n = lim_(x->a) sum_(n=1)^oo u_n (x)$ это и есть непрерывность $sum_(n=1)^oo u_n (x)$ в точке $a$
]
#example[что все плохо без равномерной сходимости (не #emoji.fire blazing #emoji.fire rust на сленге)][
$f_n (x) = x^n, E = [0,1]$

$f_n$ непрерывна в 1. $lim_(n->oo) f_n (x) = f(x) = cases(0 "при" x in [0,1), 1 "при" x = 1)$

$f$ не является непрерывной в $1$
]
#theorem[
$f_n in C [a,b], f_n arrows.rr f$ на $[a,b]$, $c in [a,b]$

Тогда $x in [a,b]$ $integral_c^x f_n (t) d t arrows.rr integral_c^x f(t) d t$

В частности $lim_(n-> oo) integral_a^b f_n (t) d t = integral_a^b f(t) d t$
]
#proof[
  
$F_n (x) := integral_c^x f_n (t) d t$ и $F(x):= integral_c^x f(t) d t$ - непрерывная функция

$abs(F_n (x) - F(x)) = abs(integral_c^c f_n (t) d t - integral_c^x f(t) d t) <= integral_c^x abs(f_n (t) - f(t)) d t <= abs(x-c) dot max_(t in [c,x]) abs(f_n (t) - f(t)) <= (b-a) sup_(t in [a,b]) abs(f_n (t) - f(t)) -> 0$
]
#theorem[
$u_n in C[a,b], sum_(n=1)^oo u_n (x)$ сходится равномерно на $[a,b]$

Тогда $integral_a^b sum_(n=1)^oo u_n (x) d x = sum_(n=1)^oo integral_a^b u_n (x) d x$
]
#proof[

  $f_n := sum_(k=1)^n u_k arrows.rr f := sum_(k=1)^oo u_k$, тогда по предудыщей теореме

$lim_(n->oo) integral_a^b sum_(k=1)^n u_k (t) d t = lim_(n->oo) sum_(k=1)^n integral_a^b f(t) d t = sum_(k=1)^oo integral_a^b u_k (t) d t = lim_(n->oo) integral_a^b f_n (t) d t = integral_a^b f(t) d t = integral_a^b sum_(k=1)^oo u_k (t) d t$
]
#warning-block[

Поточесной сходимости не достаточно

$f_n (x) = n x e^(-n x^2), E = [0,1]$

$f_n (x) ->_(n->oo) 0$, то есть $f(x) equiv 0$

$integral_0^1 f_n (x) d x = n integral_0^1 x e^(-n x^2) = n integral_0^1 e^(-n y) (d y)/2 = n/2 dot (e^(-n y))/(-n) |^(y=1)_(y=0) = (1-e^(-n))/2 -> 1/2 != integral_(0)^1 f(x) d x = 0$
]

#theorem[

$f_n in C^1 [a,b], c in [a,b], f'_n arrows.rr g$ равном. на $[a,b]$ и $f_n (c) ->_(n->oo) A in RR$

Тогда $f_n$ равномерно сходится на $[a,b]$ и $(lim_(n->oo) f_n (x))' = g(x) = lim_(n->oo) f'_n (x)$
]
#proof[

$integral_c^x g(t) d t arrows.ll f_c^x f'_n (t) d t$ из предыдущей теоремы

$integral_c^x f'_n (t) d t = f_n (x) - f_n (c) => f_n (x) = f_n (c) + integral_c^x f'_n (t) d t arrows.rr A + integral_c^x g(t) d t =: f(x) => f in C^1 [a,b]$ и $f' = g$
]
#corollary[
$u_n in C^1 [a,b]$, $c in [a,b]$, ряд $sum_(k=1)^oo u'_n (x)$ равномерно сходится, $sum_(k=1)^oo u_n (c)$ - сходится, тогда $sum_(n=1)^oo u_n (x)$ равномерно сходится на $[a,b]$ и $(sum_(n=1)^oo u_n (x))' = sum_(n=1)^oo u'_n (x)$
]
#proof[
  
$f_n := sum_(k=1)^n u_k => f'_n = sum_(k=1)^n u'_k arrows.rr sum_(k=1)^oo u'_k =: g$

$f_n (c) = sum_(k=1)^n u_k (c) -> underbrace(sum_(k=1)^oo u_k (c), = A) in RR => f_n$ равномерно сходится (то есть $sum_(k=1)^oo u_k$ равномерно сходится) и $(sum_(k=1)^oo u_k (x))'=(lim f_n (x))' = g(x) = sum_(k=1)^oo u'_k (x)$
]
#exercise[
Доказать. что ряд $sum_(n=1)^oo (sin n x)/n^2$ равномерно сходится, но почленно его дифф. нельзя
]
= Степенные ряды
#definition[
$sum_(n=0)^oo a_n (z-z_0)^n, a_n, z,z_0 in CC$ - степенной ряд
]
#definition[
Радиус сходимости степенного ряда такое $R in [0, +oo]$, что ряд $sum_(n=0)^oo a_n (z-z_0)^n$ сходится при $abs(z-z_0) < R$ и расходится при $abs(z-z_0)> R$
]
#definition[
Круг сходимости это круг $B_R (z_0) = {z in CC: abs(z-z_0) < R}$ 
]
#example[
$sum_(n=0)^oo z^n$ схоидтся при $abs(z) < 1$, расходится при $abs(z) > 1$ $=> R = 1$
]
#theorem[Теорема (формула Коши-Адомара)][
Радиус сходимости степенного ряда $sum_(n=0)^oo a_n z^n$ равен $1/(overline(lim) root(n, abs(a_n)))$]

#proof[
Напишем для ряда $sum_(n=0)^oo abs(a_n z^n)$ признак Коши

Если $overline(lim) root(n, abs(a_n z^n)) < 1$, то ряд схоидтся, $>1$, то ряд расходится и члены ряда не стремятся к нулю

$overline(lim) root(n, abs(a_n z^n)) = overline(lim) root(n, abs(a_n)) abs(z) = abs(z) overline(lim) root(n, abs(a_n))$, то есть если $abs(z) < 1/(overline(lim) root(n, abs(a_n)))$, то ряд $sum_(n=0)^oo abs(a_n z^n)$ схоидтся $=> sum_(n=0)^oo a_n z^n$ сходится

Если $abs(z) > 1/(overline(lim) root(n, abs(a_n)))$, то $a_n z^n$ не стремитяс к $0 => sum_(n=0)^oo a_n z^n$ расходится
]
#corollary[

Внутри круга сходимости ряд сходится абсолютно
]
#corollary[
  
Если ряда $sum_(n=0)^oo a_n z^n$ схоидтся при $z = z_*$, то он сходится и при $abs(z) < abs(z_*)$
]
#proof[
Из сходимости при $z = z_*$ следует, что $abs(z_*) <= R$ 
$=>$ при $abs(z) < abs(z_*) <= R$ есть сходимость
]
#corollary[
Если ряд $sum_(n=0)^oo a_n z^n$ расхоидтся при $z = z_*$, то он расходится и при $abs(z) > abs(z_*)$
]
#example[
1.
$sum_(n=0)^oo z^n/n!, R = 1/(overline(lim) root(n, 1/n!)) = 0$

$overline(lim) 1/root(n, n!) = lim 1/root(n, n!) = lim 1/root(n, n^n e^(-n) sqrt(2 pi n)) = lim 1/(n e^(-1) root(2n, 2 pi n)) = 0$

2.
$sum_(n=0)^oo n! z^n, R = 0$

3.
$sum_(n=0)^oo z^n/n, R = 1/(overline(lim) root(n, 1/n)) = 1$

$z = 1: sum_(n=0)^oo 1/n$ - расходится

$z = -1: sum_(n=0)^oo (-1)^n/n$ - сходится
]
#theorem[
$R$ - радиус сходимости степенного ряда $sum_(n=0)^oo a_n z^n, 0 < r < R$

Тогда ряд сходится равномерно в круге $abs(z) <= r$
]
#proof[
  
Ряд $sum_(n=0)^oo abs(a_n r^n)$ сходится

Если $abs(z) <= r$, то $abs(a_n z^n) <= abs(a_n r^n)$, значит и ряд $sum_(n=0)^oo a_n z^n$ сходится равномерно при $abs(z) <= r$ по признаку Вейерштрасса
]
#corollary[не ведут колобки][
$R$ - радиус сходимости степенного ряда $sum_(n=0)^oo a_n z^n, f(z)$ - его сумма при $abs(z) < R$

Тогда $f$ непрерывна при $abs(z) < R$
]
#proof[
Проверим непрерывность в точке $z_*$  $abs(z_*) < R$. Возьмем $r$, такой что $abs(z_*) < r < R$

Ряд равномерно сходится в круге $abs(z) <= r => sum_(n=0)^oo a_n z^n =: f(z)$ непрерывна в круге $abs(z) <= r$, значит непрерывна в точке $z_*$
]
#lemma[
Пусть $lim x_n = x_* in (0, +oo)$. Тогда $overline(lim) x_n y_n = x_* dot overline(lim) y_n, A:= overline(lim) x_n y_n, B:= overline(lim) y_n$
]
#proof[

существет $x_n_k y_n_k -> A => y_n_k  = (x_n_k y_n_k)/(x_n_k) -> A/(x_*) <= B$, так как $B$ - наибольший из частичных пределов для $x_n y_n$ $=> A <= x_* dot B$

Существуеют $y_n_k -> B => x_n_k y_n_k -> x_* B <= A$, так как $A$ наибольший из частичных пределов для $x_n y_n$
]
#corollary[ 
Радиуса сходимости у рядов

$sum_(n=0)^oo a_n z^n, sum_(n=1)^oo n a_n z^(n-1), sum_(n=1)^oo a_n (z^(n+1))/(n+1)$ равны
]
#proof[
Радиусы сходимости у $sum_(n=1)^oo n a_n z^(n-1)$ и $sum_(n=0)^oo n a_n z^n$ равны

но у ряда $sum n a_n z^n$ радиус сходимости равен $1/(overline(lim) root(n, n abs(a_n))) = 1/(overline(lim) root(n,n) root(n, abs(a_n))) = 1/(overline(lim) root(n, abs(a_n)))$, то есть радиус сходимости $sum_(n=0)^oo a_n z_n$
]
#theorem[почленное интегрирование степенного ряда][
$a_m in RR, x_0, x in RR$

$R$ - радиус схоидмости ряда $sum_(n=0)^oo a_n (x-x_0)^n$

Тогда при $abs(x-x_0) < R$

$integral_(x_0)^x sum_(n=0)^oo a_n (t-x_0)^n d t = sum_(n=0)^oo a_n (x-x_0)^(n+1)/(n+1)$
]
#proof[

Ряд равномерно сходится в кргуе $abs(z-x_0) <= abs(x-x_0) < R$

В частности ряд равномерно сходится на отрезке $[x_0, x]$

$=> integral_(x_0)^x sum_(n=0)^oo a_n (t-x_0)^n d t = sum_(n=0)^oo a_n integral_(x_0)^x (t-x_0)^n d t = sum_(n=0)^oo a_n (x-x_0)^(n+1)/(n+1)$
]
#definition[
$E subset CC$ и $f: E -> CC$, $a in "Int" E$

$f$ дифф. в точке $a$, если существует $k in CC$, такое что $f(z) = f(a) + k (z-a) + o(z-a)$ при $z->a$
]

#definition[
$lim_(z->a) (f(z) - f(a))/(z-a) =: f'(a)$ производная $f$ в точке $a$
]
#warning-block[
$f$ дифф в точке $a <=>$ существует $f'(a)$
]
#theorem[
$R$ - радиус сходимости ряда $sum_(n=0)^oo a_n z^n =: f(z)$ 

Тогда $f^((m)) (z) = sum_(n=m)^oo n(n-1)dots(n-m+1) a_n z%(n-m)$

$abs(z) < R$
]

#proof[

Достаточо доказать дифф $f$

$f'(z) = lim_(w->z) (f(w) - f(z))/(w-z) = lim_(w->z) 1/(w-z) dot sum_(n=0)^oo a_n (w^n - z^n) = lim_(w->z) sum_(n=0)^oo a_n (w^(n-1) + w^(n-2) z + w^(n-3) z^2 + dots + w z^(n-2) + z^(n-1)) = sum_(n=1)^oo n a_n z^(n-1)$

$o < r < R$

$abs(z) < r$ будем доказывать дифф. в такой точке $z$

$abs(w) < r => abs(a_n (w^(n-1) + w^(n-2) z + dots + z^(n-1))) <= abs(a_n) (r^(n-1) + r^(n-1) + dots + r^(n-1)) = n r^(n-1) abs(a_n)$

Для Вейерштрасса нужна сходимость ряда $sum_(n=1)^oo n r^(n-1) abs(a_n)$, то есть абс. сходимость ряда $sum_(n=1)^oo n a_n z^(n-1)$ при $z = r$ лежит в круге сходимости
]
#theorem[единственность разложения функции в степенной ряд][
Если $f(z) = sum_(n=0)^oo a_n (z-z_0)^n$ в круге $abs(z-z_0)< R$, то $a_n = (f^((n)) (z_0))/n!$
]

#proof[
  
$f^((m)) (z) = sum_(n=m)^oo n(n-1) dots (n-m+1) a_n (z-z_0)^(n-m)$

$f^((m)) (z_0) = m (m-1) dots (m-m+1) a_m = m! a_m => a_m = (f^((m)) z_0)/m!$
]
#definition[
$f$ бесконечно дифф в точке $z_0$, тогда ряд $sum_(n=0)^oo (f^((n)) (z_0))/(n!) (z-z_0)^n$ - ряд Тейлора для функции $f$ в точке $z_0$
]

#definition[
$f$ аналитическая в точке $z_0$, если $f(z) = sum_(n=0)^oo (f^((n)) (z_0))/n! (z-z_0)^n$ в окрестности точки $z_0$
]

#warning-block[
из бесконечная дифф. не следует аналитичность
]
#example[
$f(x) = cases(e^(-1/x^2) ", при" x != 0,0)$

Докажем, что $f^((n)) (x) = cases((P_n (x))/x^(3n) e^(-1/x^2),0)$ где $P_n (x)$ - многочлен

Индукция. База $n=0$

Переход $n-> n+1$ пусть $x != 0$

$f^((n+1))  (x) = (P_n (x) x^(-3n) e^(-1/x^2))' = P'_n (x) x^(-3n) e^(-1/x^2) + P_n (x) (-3n) x^(-3n-1) e^(-1/x^2) + P_n (x) x^(-3n) e^(-1/x^2) 1/x^3 = e^(-1/x^2) (x^3 P'_n (x) - 3 n x^2 P_n (x) + P_n (x))/x^(3n+3)$

$f^((n+1)) (0) = lim_(x->0) (f^((n)) (x) - f^((n)) (0))/(x-0) = lim_(x-> 0) (P_n (x))/(x^(3n+1)) e^(-1/x^2)  = | y = 1/x | = lim_(y -> oo) y^(3n+1) e^(-y^2) P_n (1/y) = 0$

В нуле нет аналитичности 

$f^((n)) (0) = 0, sum_(n=0)^oo (f^((n)) (0))/n! x^n equiv 0$
]

#definition[Разложение элементарных функций в ряд Тейлора][

$exp x = sum_(n=0)^oo x^n/n!, R = oo, cos x = sum_(n=0)^oo ((-1)^n x^(2n))/(2n)!, R = oo$

$sin x = sum_(n=0)^oo ((-1)^n x^(2n+1))/(2n+1)!, R = oo$
]
#definition[
$1. exp z := sum_(n=0)^oo z^n/n!$

$2. cos z = sum_(n=0)^oo ((-1)^n z^(2n))/(2n)!$

$3. sin z = sum_(n=0)^oo ((-1)^n z^(2n+1))/(2n+1)!$
]
#note-block[
$exp (i z) = cos z + i sin z$

$cos z = (exp z + exp(-z))/2, sin z = (exp (i z) + (exp(-i z)))/(2i)$
]
#exercise[
Доказать, что $cos^2 + sin^2 = 1$

$4. ln (1+x) = sum_(n=1)^oo ((-1)^(n-1) x^n)/n$ при $x in (-1,1)$

$5. arctan x = sum_(n=0)^oo (-1)^n x^(2n+1)/(2n+1)$ при $x in (-1,1)$
]
#proof[
$ln(1+x) = integral_0^x (d t)/(1+t) = integral_0^x sum_(n=0)^oo (-t)^n d t = sum_(n=0)^oo integral_0^x (-t)^n d t = sum_(n=0)^oo ((-1)^n x^(n+1))/(n+1)$

$arctan x = integral_0^ x (d t)/(1+t^2) = integral_0^x sum_(n=0)^oo (-1)^n t^(2n) d t = sum_(n=0)^oo (-1)^n (x^(2n+1))/(2n+1)$
]
#definition[Нисходящая факториальная степень][

$p^underline(n) := p (p-1) (p-2) dots (p-n + 1)$

Замечание $n^underline(n) = n!, C_n^m = n^underline(m)/m!$

$6. (1+x)^p = sum_(n=0)^oo (p^underline(n))/n! x^n$ при $x in (-1,1)$
]
#theorem[
+ Радиус сходимости ряда $ sum_(n=0)^oo (p^underline(n))/n! x^n$ равен 1
+ Если $f(x) :=  sum_(n=0)^oo (p^underline(n))/n! x^n$ при $x in (-1,1)$, то $f'(x) dot (1+x) = p f(x)$
+ сама формула
]
#proof[
Посчитаем $lim root(n, abs(p^underline(n))/n!) = lim a_(n+1)/a_n$ (если предел справа существует) $= lim abs(p^underline(n+1))/(n+1)! dot abs((n!)/p^underline(n)) = lim abs((p-n)/(n+1)) = 1$

$=> R = 1/(overline(lim) root(n, a_n)) = 1$

$f'(x) = sum_(n=1)^oo p^(underline(n))/n! n x^(n-1)$

$(1+x) f'(x) = sum_(n=1)^oo p^underline(n)/(n-1)! x^(n-1) + sum_(n=0)^oo p^(underline(n))/n! n x^(n) $ (начинаем индекс с 0 в первой сумме) $= sum_(n=0)^oo x^n/n! (p^underline(n+1) + n p^underline(n)) = p sum_(n=0)^oo p^underline(n)/n! x^n = p f(x)$

3.
$g(x) := f(x) dot (1+x)^(-p)$

Надо доказать, что $g equiv 1$ при $x in (-1,1)$

$g(0) = f(0) = 1$

$g'(x) = f'(x) (1+x)^(-p) + f(x) (-p) (1+x)^(-p-1) = (p f(x))/(1+x) (1+x)^(-p) + f(x) (-p) (1+x)^(-p-1) = 0$
]
#note-block[Частный случай
$p = -1/2$

$1/sqrt(1+x) = sum_(n=0)^oo (-1)^n (C_(2n)^n)/4^n x^n$


$7. arcsin x = sum_(n=0)^oo (C_(2n)^n)/4^n x^(2n+1)/(2n+1)$
]

#proof[
$arcsin x = integral_(0)^x (d t)/sqrt(1-t^2) = integral_0^x sum_(n=0)^oo (-1)^n (C_(2n)^n)/4^n (-t^2)^n d t = sum_(n=0)^oo (C_(2n)^(n))/4^n integral_0^x t^(2n) d t = sum_(n=0)^oo (C_(2n)^n)/4^n x^(2n+1)/(2n+1)$
]

#text(fill: white)[
  Тюрьма.
  
  Зеки на прогулке.
  
  Молодой Зек подходит к старому Зеку и говорит: 
  
  -- Что то я не понимаю теорию относительности: 
  
  Старый Зек:
  
  -- Вот мы с тобой ходим а на самом деле мы сидим 
]


= Дифф. исчесление функций многих переменных

== Дифференцируемость

#definition[
$f: E -> RR^n, E subset RR^m, a "Int" E$

$f$ - диффф. в точке $a$, если существует лин. отображение  $T: RR^m -> RR^n$, для которого $f(a + h) = f(a) + T h + o(norm(h)), h -> 0$
]
#remark[
то есть $f(a + h) = f(a) + T h + alpha(h) dot norm(h), alpha: E -> RR^n and alpha(h) ->_(h->0) 0$
]
#definition[
Этот оператор $T$ - дифференциал функции $f$ в точке $a$ и обозначается $d_a f$
]
#definition[
Матрица лин. оператора $d_a f$ называется матрицей Якоби и обозначается $f' (a)$
]
#warning-block[
Если $f$ дифференцируема, то $T$ определено однозначно

Зафиксируем $h in RR^m$

$lim_(t->0, t in RR) (f(a + t h) - f(a))/t = lim_(t->0) (f(a) + T (t h) + o(norm(t h)) - f(a))/t = lim_(t->0) (t T h + t o(norm(h)))/t = T h$
]
#proposition[
Если $f$ дифференцируема, то $f$ непрерывна в точке $a$
]
#proof[
$lim_(h->0) f(a+h) = lim_(h->0) (f(a) + T h + alpha(h) dot norm(h)) = f(a)$
]


#note-block[
Важный частный случай
  
$n = 1$

$T$ - лин. отобр из $RR^m$ в $RR^m$ Как они устроены?

Это скалярное произв. с некоторым вектором $v in RR^m$

$f(a + h) = f(a) + chevron.l v, h chevron.r + o(norm(h)), h -> 0$
]
#definition[$V$ называется градиентом функции $f$ в точке $a$. Обозначается либо $gradient f(a)$ либо $"grad" f(a)$]

#example[
  + Если $f equiv "const"$, то $f$ - дифф. $f(a+h) = f(a) + T h + o(norm(h)) = f(a)$
  + Если $f$ линейное отображение из $RR^m$ в $RR^n$, то $f$ - дифф. $f(a+h) = f(a) + f(h) = f(a) + T h + o(norm(h)) = f(a) + f(h)$
]

#theorem[$f: E -> RR^n, E subset RR^m, a in "Int" E, f = vec(f_1, f_2, dots.v,f_n)$

$f$ дифф в точке $a <=> f_k$ дифф. в точке $a$ при $k = 1,2,dots,n$
] <theorem:8>

#proof[Proof of @theorem:8][
  
  "$==>$"

  $f(a+h) = f(a) + T h + alpha(h) dot norm(h), alpha(h) ->_(h->0) 0$

  Запишем покоординатно $f_k (a+h) = f_k (a) + T_k h + alpha_k (h) dot norm(h)$, надо доказать, что $alpha_k (h) ->_(h->0) 0$

  $abs(alpha_k (h)) <= sqrt((alpha_1 (h)^2 + dots + (alpha_n (h))^2)) = norm(alpha_h) ->_(h->0) 0$

  "$<==$"

  $f_k$ дифф. в точке $a$ $=> f_k (a+h) = f_k (a) + T_k h + alpha_k (h) dot norm(h)$, где $alpha_k (h) ->_(h->0) 0$

  соберим из них векторное равенство $f(a+h) = f(a) + T h + alpha(h) dot norm(h)$

  Надо доказать, что $norm(alpha(h)) -> 0, norm(alpha(h)) = sqrt((alpha_1 (h))^2 + dots + (alpha_n (h))^2) <= abs(alpha_1 (h)) + dots + abs(alpha_n (h)) -> 0$

]

#corollary[Строки матрицы Якоби $f(a)$ - это градиенты координатных функций $gradient f_k (a)$]


#definition[
  $f: E -> RR, E subset RR^m, a in "Int" E, h in RR^m, norm(h) = 1$
 производная по направлению $h$

  $(partial f)/(partial h) (a) := lim_(t->0, r in RR) (f(a+ t h) - f(a))/t$
]

#theorem[
  $f: E -> RR, E subset RR^m, a in "Int" E, f$ дифф в точка $a$, $h in RR^m, norm(h) = 1$

  Тогда $(partial f)/(partial h) (a) = dif_a f(h) = chevron gradient f(a), h chevron.r$
]

#proof[
  Первое равенство уже обсуждали, второе равенство тоже обсуждали
]

#corollary[Экстремальное свойство градиента][
  $f: E -> RR, a in "Int" E, f$ - дифф в точке $a$ и $gradient f(a) != 0$

  Тогда $abs((partial f)/(partial h) (a)) <= norm(gradient f(a))$
  и равенствро достигается $<=> h = plus.minus (gradient f(a))/(norm(gradient f(a)))$
] <corollary:eg>
#proof[Proof of @corollary:eg][
 $abs((partial f)/(partial h) (a)) = abs(chevron gradient f(a)"," h chevron.r) <= norm(gradient f(a)) dot norm(h) = norm(gradient f(a))$ 

 Равенство в Коши-Буняковском $<=>$ векторы сонаправлены, то есть $h = c dot gradient f(a)$ и т.к. $norm(h) = 1: h = plus.minus (gradient f(a))/(norm(gradient f(a)))$
]

#definition[
  $e_k = vec(0, dots.v, 0,1,0,dots.v,0), 1$ на $k$-ом месте, $f: E -> RR, a in "Int" E$

  Частная производная функции $f$ в точке $a$

  $(partial f)/(partial e_k) (a)$

  Обозначение $(partial f)/(partial x_k) (a)$ или $f'_(x_k) (a)$
]

#corollary[
  $gradient f(a) = ((partial f)/(partial x_k) (a), dots, (partial f)/(partial x_m) (a))$, то есть градиент - вектор, составленный из частных производных
] <corollary2:as>

#proof[Proof of @corollary2:as][
$chevron gradient f(a), e_k chevron.r = (partial f)/(partial e_k) (a) = (partial f)/(partial x_k) (a)$  
]

#corollary[
  $f: E -> RR^n, a in "Int" E, f$ дифф в точке $a$

  Тогда $f'(a) = mat(partial(f_1)/(partial x_1) (a), (partial f_1)/(partial x_2) (a), dots, (partial f_1)/(partial x_m) (a); dots, dots, dots, dots; partial(f_1n)/(partial x_1) (a), (partial f_n)/(partial x_2) (a), dots, (partial f_n)/(partial x_m) (a);)$
] <corollary3:as>

#example[
  $f(x,y) = x^y, x in (0, +oo), y in RR$

  $(partial f)/(partial x) = y dot x^(y-1), (partial f)/(partial y) =  x^y ln x$
]

#theorem[линейность дифференцируемости][
  $f,g : E-> RR^n, a in "Int" E, f$ и $g$ дифф в точке $a$, $lambda in RR$

  Тогда $f+ g$ и $lambda f$ дифф в точке $a$ и $dif_a (f+g) = dif_a f + dif_a g, dif_a (lambda f) = lambda dif_a f$ (для матрицы Якоби $(f+g)' = f' + g'$ и $(lambda f)' = lambda f'$) 
] <theorem:lindif>

#proof[Proof of @theorem:lindif][
  $f(a + h) = f(a) + dif_a f(h) + lambda(h) norm(h)$, где $lambda(h) -> 0$

  $g(a + h) = g(a) + dif_a g(h) + beta(h) norm(h)$, где $beta(h) -> 0$

  $f(a+h) + g(a+h) = f(a) + g(a) + underbrace(dif_a f(h) + dif_a g(h), "лин. отобр") + underbrace((lambda(h) + beta(h)), ->0) norm(h)$
]

#theorem[дифф. композиции][
  $f: D -> RR^m, D subset RR^l, g : E -> RR^n, E subset RR^m, a in "Int" D, f(D) subset E, f(a) in "Int" E$. $f$ дифф в точке $a$, $g$ дифф в точке $f(a)$

  Тогда $g compose f$ дифф в тчоке $a$ и $dif_a (g compose f)(h) = d_(f(a)) g(d_a f(h))$ (в терминах матрицы Якоби $(g compose f)'(a) = g' (f(a)) dot f'(a)$ )
] <theorem:difcomp>

#proof[Proof of @theorem:difcomp][
  
  $b:= f(a), f(a + h) = underbrace(f(a), =b ) + underbrace(dif_a f(h) + alpha(h) dot norm(h), =:k )$, где $alpha(h) -> 0$

  $g(b+ k) = g(b) + dif_b g(k) + beta(k) dot norm(k)$, где $beta(k) -> 0$

  Проверим, что $k-> 0$ при $h -> 0$

  $norm(k) = norm(dif_a f(h) + alpha(h) norm(h)) <= underbrace( norm(d_a f(h)), <= norm(d_a f) norm(h) ) + norm(alpha(h) norm(h)) <= norm(h) (norm(d_a f) + norm(alpha(h))) <= C dot norm(h)$

  $g(f(a+h)) = g(b+k) = g(b) + underbrace(dif_b g(k), = dif_b g( dif_a f(h)) + dif_b g(alpha(h) norm(h)) ) + beta(k) norm(k) = g(f(a)) + underbrace(dif_f(a) g(dif_a f(h)), "лин. отобр") + underbrace(dif_b g(alpha(h)) norm(h) + beta(k) norm(k), "надо доказать, что" o(norm(h)))$

  $dif_b g(alpha(h)) -> d_b g(0) = 0$

  Осталось понять, что $beta(k) norm(k) = o(norm(h))$, то есть

  $(beta(k) norm(k))/norm(h) -> 0$, так как $(abs(beta(k))norm(k))/norm(h) <= (abs(beta(k)) C norm(h))/norm(h) = C abs(beta(k)) -> 0$
]

#theorem[дифф произведения скалярной и векторной функий][
  $E subset RR^m, a in "Int" E, f: E -> RR^n$ дифф в точке $a$, $lambda: E -> RR$ дифф в точке $a$

  Тогда $lambda f$ дифф. в точке $a$ и $dif_a (lambda f) (h) = dif_a lambda(h) dot f(a) + lambda(a) dif_a f(h)$ (в терминах матриц. Якоби $(lambda f)' (a) = f(a) lambda'(a) + lambda(a) f'(a)$)
]

#proof[
  
  $f(a+h) = f(a) + dif_a f(h) + alpha(h) norm(h)$, где $alpha(h) -> 0$

  $lambda(a+h) = lambda(a) + dif_a lambda(h) + beta(h) norm(h)$, где $beta(h) -> 0$

  $lambda(a+h) f(a+h) = underline(lambda(a) f(a)) + underline(lambda(a) dif_a f(h)) + lambda(a) alpha(h) norm(h) + underline(dif_a lambda(h) f(a)) + dif_a lambda_h dif_a f(h) + dif_a lambda(h) alpha(h) norm(h) + beta(h) norm(h) f(a) + beta(h) norm(h) dif_a f(h) + beta(h) alpha(h) norm(h)^2$

  Осталось доказать, что остальное $= o(norm(h))$, некоторые очев, что $o$ (мне лень писать)

  Проверим, что $dif_a lambda(h) d_a f(h) = o(norm(h))$

  $norm(d_a lambda_h d_a f(h))/(norm(h)) = (abs(d_a lambda_h)  dot norm(d_a f(h)))/norm(h) <= norm(d_a f) dot abs(d_a lambda(h))$
]

#theorem[дифф. скалярное произв.][
  $f,g: E -> RR^n, a in "Int" E, f$ и $g$ дифф в точке $a$

  Тогда $chevron f, g chevron.r$ дифф. в точке $a$ и $dif_a chevron f, g chevron.r (h) = chevron d_a f(h), g(a) chevron.r + chevron f(a), dif_a g(h) chevron.r$
]

#proof[

  $chevron f, g chevron.r = sum_(k=1)^n f_k g_k, dif_a chevron f, g chevron.r = sum_(k=1)^n dif_a (f_k g_k)$

  $f_k g_k$ дифф. в точке $a$ по пред. теореме

  $d_a (f_k g_k)(h) = dif_a f_k (h) g_k (a) + f_k (a) d_a g_k (h)$

  Осталось эту черемшу просуммировать и получим то, что хотели
]

= Непрерывная дифференцируемость

#theorem[
  $f: E -> RR, a in "Int" E$

  Если все частные производные $f$ сущ. в окрестночти $a$ и непрерывна в точке $a$, то $f$ дифф. в точке $a$
]

#proof[
  
  $h in RR^m$ маленький

  $b_k := vec(a_1 + h_1, dots.v, a_k + h_k, a_(k+1), dots.v, a_m), b_0 = a, b_m = a +h$

  $R(h):= f(a+h) - f(a)-sum_(k=1)^n (partial f)/(partial x_k) (a) h_k =^? o(norm(h))$

  $F_k (t) := f(b_(k-1) + t h_k e_k)$ определены при $t in [0,1]$

  $F_k (0) = f(b_(k-1))$ и $F_k (1) = f(b_k)$

  $F(k) (1) - F_k (0) =_"Лагранж" (1-0) dot F'_k (theta_k), theta_k in (0,1) = (partial f)/(partial x_k) (b_(k-1) + theta_k h_k e_k) h_k$

  $f(a+h) - f(a) = f(b_m) - f(b_0) = sum f(b_k) - f(b_(k-1)) = sum F_k (1) - F_k (0) = sum (partial f)/(partial x_k) (b_(k-1) + theta_k h_k e_k) h_k$

  $abs(R(h)) = abs(sum ((partial f)/(partial x_k) (b_(k-1) + theta_k h_k e_k) - (partial f)/(partial x_k) (a)) dot h_k) <= (sum h_k^2)^(1/2) dot (sum ((partial f)/(partial x_k) (b_(k-1) + theta_k h_k e_k) - (partial f)/(partial x_k) (a))^2)^(1/2)$

  то есть, что $sum ( (partial f)/(partial x_k) (b_(k-1) + theta_k h_k e_k) - (partial f)/(partial h) (a))^2 -> 0$

  $(partial f)/(partial x_k) (b_(k-1) + theta_k h_k e_k) -> (partial f)/(partial x_k) (a)$
]

#note-block[
  Непрерывность $(partial f)/(partial x_1)$ в точке $a$ не использовалась

  $f(b_1) = f(a+h_1 e_1) = underbrace(f(a), f(b_0)) + (partial f)/(partial x_1) (a) h_1 + o(h_1)$

  $f(b_1) - f(b_0) = (partial f)/(partial x_1) (a) h_1 + o(norm(h))$
]

#warning-block[
  Из дифф. $f$ в точке $a$ не следует существование частных производных в окрестности
]

#example[
  $f(x,y) = cases(x^2 + y^2 ", если ровно одно из чисел рационально", 0 ", иначе")$

  Эта функция дифф. в нуле

  $f(x,y) = f(0,0) + T(x,y) + o(sqrt(x^2 + y^2)), f(x,y) <= x^2 + y^2$, если $T(x,y) = 0$ тогда формула верная

  $O(x^2 + y^2) = f(x,y) = o(sqrt(x^2 + y^2))$

  Зафиксируем $x_0 != 0$ и рассмотрим функцию $f(x_0 ,y) = cases(0, >= x_0^2 > 0)$
]

#definition[
  $f: E -> RR^n, a in "Int" E$

  $f$ непрерывно дифф в точке $a$, если $f$ дифф в окрестности точки $a$ и $norm(dif_x f - dif_a f) -> 0$
]

#theorem[
  $f: E -> RR^n, a in "Int" E$ 
  
  Тогда $f$ непрерывна дифф в точке $a$ $<=> cases(f "дифф в окрестности" a, "все частные производные всех координат функций непрерывны в точке " a)$, то есть в матрице Якоби все коэфф. непрерывны в точке $a$
]

#proof[

  "$<==$"

  $norm(dif_x f - dif_a f)^2 <= sum_(i=1)^m sum_(j=1)^n ((partial f_j)/(partial x_i) (x) - (partial f_j)/(partial x_i) (a))^2 -> 0 $

  "$==>$"

  $abs( (partial f_j)/(partial x_i) (x) - (partial f_j)/(partial x_i) (a)) <= norm( dif_x f(e_i) - d_a f(e_i)) = norm((d_x f - d_a f) e_i) <= norm(d_x f - d_a f) (e_i)$
]

#theorem[

  Непрерывная дифф сохраняется при лин. комп, умножении, композиции
]

= Частные производные высших порядков

#definition[
$f: E -> RR, a in "Int" E$

Предположим, что $(partial f)/(partial x_i)$ существует в окрестности точки $a$

$(partial f)/(partial x_i) : $ окрестность точки $a -> RR$

Если у нее существует частная производная $(partial)/(partial x_i)$, то $(partial)/(partial x_j) ((partial f)/(partial x_i))$ называется частной производной второго порядка по $x_i$ и $x_j$

Обозначение $(partial^2 f)/(partial x_j partial x_i):= partial/(partial x_j)((partial f)/(partial x_i)) $

$f''_(x_i x_j) := (f'_(x_i))'_(x_j)$
]

#note-block[
  Сколько производных порядка $r?$ $m^r$
]

#example[
$f(x,y) = x^y$

$f'_x = y dot x^(y-1)$

$f'_y = x^y ln x$

$(f'_x)'_y = (y x^(y-1))'_y = x^(y-1) + y x^(y-1) ln x$

$(f'_y)'_x = (x^y ln x)'_x = y^(x-1) x ln x + x^y 1/x$

$f''_(x y) = f''_(y x)$
]


#example[
  $f(x,y) = cases(x y dot (x^2 -y^2)/(x^2+y^2) "," x^2 + y^2 != 0, 0)$

  при $x^2 + y^2 != 0$  $f'_x (x,y) = y dot (x^2 -y^2)(x^2 + y^2) - x y dot (2 x (x^2 + y^2) - 2x (x^2-y^2))/(x^2 + y^2)^2 = y dot (x^2 -y^2)/(x^2+y^2) + (4 x^2 y^2)/(x^2+y^2)^2$

  $f'_x (0,0) = lim_(y->0) (f(0,y) - f(0,0))/y = 0$

  $f''_(x y) (0,0) = lim_(y->0) (f'_x (0,y) - f'_x (0,0))/y = lim_(y->0) (y (0^2-y^2)/(0+y^2)) dot 1/y = -1$

  $f''_(y x) (0,0) = 1$
]

#theorem[
  $f: E -> RR, (x_0, y_0) in "Int" E$

  $f'_x, f'_y$ и $f''_(x y)$ существует в окрестности точки $(x_0, y_0)$ и $f''_(x y)$ непрерывны в точке $(x_0, y_0)$

  Тогда $f''_(y x) (x_0, y_0)$ существует и $f''_(x y) (x_0, y_0) = f''_(y x) (x_0, y_0)$
]
#proof[
  $phi(s):= f(s, y_0 + k) - f(s, y_0)$

  $ phi(x_0 + h) - phi(x_0) = h phi'(x_0 + theta h) $ для некотррого $theta in (0,1)$ (Лагранж)

  $ = h (f'_x (x_0 + theta h, y_0 + k) - f'_x (x_0 + theta h, y_0)) = h k f''_(x y) (x_0 + theta h, y_0 + overline(theta) k) = h k (f''_(x y) (x_0,y_0) + alpha(h,k)) $, где $alpha(h,k) ->_((h,k) ->0) 0$, то есть $abs(alpha(h,k)) < epsilon$ для маленьких $h$ и $k$

  $abs(1/h (phi(x_0+h)/k - phi(x_0)/k) - f''_(x y) (x_0, y_0)) < epsilon$ при $h$ и $k$ близких к нулю

  $phi(x_0)/k = (f(x_0,y_0 + k) - f(x_0, y_0))/k -> f'_y (x_0, y_0)$

  $phi(x_0 + h)/k = f'_y (x_0 + h, y_0)$

  $=> abs(underbrace((f'_y (x_0, y_0) - f'_y (x_0, y_0))/h, ) - f''_(x y) (x_0, y_0)) <= epsilon$ при $h$ близких к нулю $o$

  $=> underbrace( lim_(h->0) (f'_y (x_0 + h, y_0) - f'_y (x_0, y_0))/h, (f'_y)'_x (x_0, y_0) )= f''_(x y) (x_0, y_0)$
]

#definition[
  $f: D -> RR$, $D$ - открытое множество

  $f$ $r$ раз дифф. в $D$,

  Если все частные производные до $r$-ого порядка включительно существуют и непрерывны

  Обозначение $f in C^r (D)$
]

#corollary[
  Если $f in C^r (D), i_1, i_2, dots i_r$ перестановка $j_1, j_2, dots, j_r$, то $ (partial^r f)/(partial x_j_r partial x_j_(n-1) dots partial x_j_1) = (partial^r f)/(partial x_i_r partial x_i_(r-1) partial x_i_1) $
]

#proof[
  Достаточно доказать, что для транскозиции $(j_1, j_2, dots, j_(k-1), j_(k+1), j_k, j_(k+2), dots j_r)$

  $g := (partial^(k-1) f)/(partial j_(k-1) partial j_(k+2) dots partial j_1)$, $r-k+1$ непр. дифф. $(partial^2 g)/(partial x_j_(k+1) partial x_j_k) = (partial^2 g)/(partial j_k partial x_(j)_(k+1))$ и дифф. по $(partial^(r-k+1))/(partial x_j_r dots partial x_j_(k+2))$
]

#definition[
  Мультииндексы $k = (k_1, k_2, dots, k_m), k_1, k_2, dots, k_m$ - неотрицательные целые

  Высота мультииндекса $abs(k):= k_1 + k_2 + dots + k_m$

  $k! = k_1 ! k_2 ! dots k_m !$

  Если $h in RR^m$, то $h^k := h_1^(k_1) h_2^(k_2) dot dots dot h_m^(k_m)$

  Если $f: D -> RR$, то $f^((k)) := (partial^abs(k) f)/((partial x_m)^(k_m) (partial x_(m-1))^(k_(m-1)) dots (partial x_1)^(k_1))$
]

#note-block[
  $C_(abs(k))^(k_1, k_2, dots, k_m) = (abs(k)!)/(k_1 ! k_2 ! dots k_m !) = (abs(k)!)/k!$
]

#lemma[
  $f: D -> RR, [x, x+h] in D$

  $f in C^r (D), F(t):= f(x + t h)$

  $F: [0,1] -> RR$

  Тогда $F in C^r [0,1]$ и $F^((r)) (t) = sum_(abs(k) = r) (r!)/k! f^((k)) (x + t h) h^k$
]

#proof[
  $g: D -> RR, g in C^1 (D), G(t):= g(x+t h)$

  $G'(t) = g'(x+t h)(x+ t h)' = (g'_(x_1) (x+ t h), dots g'_x_m (x + t h)) vec(h_1, h_2, dots.v, h_m) = sum_(i=1)^m g'_x_i (x + t h) h_i$

  $F^((r)) (t) = sum_(i_r = 1)^m sum_(i_(r-1) = 1)^m dots sum_(i_1 = 1)^m (partial f^r)/(partial x_i, partial x_i_2, dots, partial_i_r) (x+ t h) h_i_1 h_i_2 dots h_i_m = $

  $k:= (\#{j:i_j = 1 }, \#(j:i_j = 2), dots, \#{j: i_j = m})$

  $= sum_(abs(k) = r) r!/k!  f^((k)) (x + t h) h^k$
]

#definition[
  формула Тейлора с остатком в форме Лагранжа $f: D -> RR, [x, x+h] subset D, f in C^r (D)$

  Тогда $f(x+h) = sum_(k<= r-1) (f^((k)) (x))/k! h^k + sum_(abs(k) = r) (f^((k)) (x + theta h))/(k!) h^k$ для некоторого $theta in (0,1)$
]

#proof[
  $F(t) := f(x + t h)$

  $ F(1) = sum_(l = 0)^(r-1) (F^((l))(0))/(l!) dot 1^l + (F^((r) (theta)))/r! dot 1^r $

  $ sum_(l=0)^(r-1) 1/l! sum_(abs(k) = l) l!/k! f^((k)) (x) dot h^k + 1/r! sum_(abs(k) = r) r!/k! f^((k)) (x+ theta h) h^k $

  $ sum_(abs(k) <= r-1) (f^((k)) (x) )/k! dot h^k $
]

#definition[
  Многомерная формула Тейлора с остатком в форме Пеано $f: D -> RR, [x,x+h] subset D, f in C^r (D)$

  Тогда $f(x+h) = sum_(abs(k) <= r-1) (f^((k)) (x))/k! h^k + o(norm(h)^r)$ при $h-> 0$
]

#proof[

  $f(x+h) = sum_(abs(k) <= r) (f^((k) (x)))/k! h^k + underbrace( sum_(abs(k) = r) ((f^((k))(x+theta h))/k! h^k - (f^((k)) (x))/k! h^k), =^? o(norm(h)^k) )$

  $h^k/norm(h)^r = (h_1^(k_1) h_2^(k_2) dots h_m^(k_m))/(norm(h)^(k_1) norm(h)^(k_2) dots norm(h)^(k_m)) => norm(h^k)/norm(h^r) <= 1$

  Надо доказать, что $lim_(h->0) 1/norm(h)^r (f^((k)) (x+ theta h) - f^((k)) (x)) h^k = 0$
]

= Обратная и неявная функции

#theorem[Банаха о сжатии][
  $(X, rho)$ - полное метрическое пространство

  $f: X -> X$ сжатие с коэфф. $lambda in (0,1)$, такое что $rho(f(x), f(y)) <= lambda rho(x,y) forall x, y$

  Тогда у $f$ существует единственная неподвижная точка $x_*$. Более того, если $x_n = f(x_(n-1))$,то $x_n -> x_*$
 ]

#proof[
  Единственность

  $f(x_*) = x_*$ и $f(y_*) y_*$, то $rho(x_*, y_*) = rho(f(x_*), f(y_*)) <= lambda rho(x_*, y_*)$ - противоречие

  Существование

  Возьмем $x_0 in X$ и будем итерировать: $x_(n+1) = f(x_n)$

  Давайте проверим, что $x_n$ - фундаментальная последовательность

  $rho(x_n, x_(n+k)) = rho(f(x_(n-1)), f_(x+k-1)) <= lambda rho(x_(n-1), x_(n+k-2)) <= lambda^2 (x_(n-2), x_(n+k-2)) <= dots <= lambda^n rho(x_0, x_k) = (rho(x_0, x_1))/(1-lambda) dot lambda^n$

  $rho(x_0, x_k) <= rho(x_0, x_1) + rho(x_1, x_2) + dots + rho(x_(k-1), x_k) <= (1+lambda + lambda^2 + dots + lambda^(k-1)) rho(x_0, x_1) <= 1/(1-lambda)(rho(x_0, x_1))$

  Проверим, что $f(x_*) = x_*: f(x_*) = f(lim x_n) = lim f(x_n) = lim x_(n+1) = x_*$
]

#corollary[
  $x_(n+1) = f(x_n)$, тогда $phi(x_n, x_*) <= lambda^n/(1-lambda) (phi x_0, x_1)$ $x_*$ - неподвижная точка
]

#corollary[
  $X$ - полное метрическое пространство, $g, f: X -> X$ - сжатия с коэффициентом $lambda in (0,1)$. $x_*$ и $y_*$ их неподвижные точки

  Тогда $phi(x_*, y_*) <= (rho(f(x_*), g(x_*)))/(1-lambda)$
]

#proof[
  $rho(x_*, y_*) = rho(f(x_*), g(x_*)) <= rho(f(x_*), g(x_*)) + underbrace(rho(g(x_*), g(y_*)), <= lambda rho(x_*, y_*))$

  $(1-lambda)rho(x_*, y_*) <= rho(f(x_*), g(x_*))$
]

#note-block[
  $A: RR^n -> RR^n$ линейный оператор, обратимый

  Тогда $norm(A x) >= (norm(x))/(norm(A^(-1)))$

  $x = A^(-1)(A x), norm(x) = norm(A^(-1) (A x)) <= norm(A^(-1)) dot norm(A x)$
]

#theorem[
  $A: RR^n -> RR^n$ и $norm(A x) >= m norm(x) forall x in RR^n$

  Тогда $A$ обратим и $norm(A^(-1)) <= 1/m$
]

#proof[
  Надо понять, что $A x = 0$ имеет только нулевое решение

  $0 = norm(A x) >= m norm(x) => norm(x) = 0 => x = 0$

  $x = A y$
  
  $norm(A^(-1) x) = norm(A^(-1) (A y)) = norm(y) <= (norm(A y))/m = norm(x)/m$

  $norm(A^(-1)) = sup_(x!=0) norm(A^(-1) x)/norm(x) <= 1/m$
]

#theorem[Об обратимости операторов, близких к обратимым][
  $A: RR^n -> RR^n$ обратимый лин. оператор. $B: RR^n -> RR^n$ лин. оператор, такой что $ norm(B - A) < 1/(norm(A^(-1))) $ 

  Тогда
  + $B$ - обратим и $B^(-1) <= 1/(1/norm(A^(-1))-norm(B-A))$

  
  + $norm(B^(-1) - A^(-1)) <= (norm(B-A) norm(A^(-1)))/(1/norm(A^(-1)) - norm(B-A))$
]

#proof[
  1. $norm(B x) = norm(A x + (B - A) x) >= underbrace( norm(A x), >= norm(x)/norm(A^(-1)) ) - underbrace(norm((B-A) x), <= norm(B-A)dot norm(x)) >= norm(x) underbrace( (1/norm(A^(-1)) - norm(B-A)), =:)$

  2. $B^(-1) - A^(-1) = B^(-1)(A-B)A^(-1)$

  $norm(B^(-1) - A^(-1)) <= norm(B^(-1)) norm(A - B) norm(A^(-1)), norm(B^(-1)) <= 1/(1/norm(A^(-1)) - norm(B - A))$
]

#corollary[
  $A: RR^n -> RR^n$ обратимый линейный оператор, $B_j : RR^n -> RR^n$, такие что $B_j -> A$ (то есть $norm(B_j - A) -> 0$)

  Тогда $B_j^(-1) -> A^(-1)$ (то есть $norm(B_j^(-1) - A^(-1)) -> 0$)
]

#proof[
  $norm(B_j^(-1) - A^(-1)) <= (norm(B_j - A) norm(A^(-1)))/(1/norm(A^(-1))- norm(B_j - A)) -> 0$
]

#theorem[
  $f: B_r (a) -> RR^n$ и $norm(d_* f) <= C forall x in B_r (a)$

  Тогда $forall x,y in B_r (a): norm(f(x) - f(y)) <= C norm(x-y)$
]

#proof[
  $phi(t):= chevron f(x+t(y-x)), f(y)-f(x) chevron.r, phi: [0,1] -> RR$, $phi$ дифф. функция $phi'(t) = chevron f'(x+t(y-x)) dot (y-x), f(y) - f(x) chevron.r$

  $phi(1) - phi(0) = chevron f(y), f(y) - f(x) chevron.r - chevron f(x), f(y) - f(x) chevron.r = norm(f(y) - f(x))^2$

  Можно считать, что $f(x) != f(y)$

  $norm(f(y) - f(x))^2 = phi(1) - phi(0) = phi'(theta) = chevron f'(x+theta(y-x))(y-x), f(y) - f(x) chevron.r <= norm(underbrace(f'(x+theta(y-x)), <= norm(d_(x+theta(x-y)) f) norm(y-x) <= C norm(y-x)) dot (y-x) ) dot norm(f(y) - f(x)) <= C norm(y-x) norm(f(y) - f(x))$
  

]

#theorem[об обратной функции][
  $f: D -> RR^n, D$ - открыто, $a in D$, $f$ непрерывное дифф, $d_a f =: A$ - обратим.

  Тогда существует $U$ и $V$ - окрестности точек $a$ и $b:= f(a)$, такое что $f: U -> V$ биекция и $f^(-1): V -> U$ - непрерывно дифф. отображение

  Типо можем локально обратить функцию
]

#proof[Часть 1][
Существование окрестностей и непрер. $f^(-1)$

Возьмем такое $r>0$, что $norm(A^(-1)) norm(f'(x) - A) < 1/2 forall x in B_r (a)$

$G_y (x):= x + A^(-1)(y - f(x))$ ($y$ фиксировано)

$G'_y (x) = E + A^(-1)(-f'(x)) = E - A^(-1)(f'(x)) = A^(-1) (A - f'(x))$

$norm(G'_y (x)) <= norm(A^(-1)) norm(A-f'(x)) < 1/2$ если $x in overline(B)_r (a)$

по предыдущей теореме если $x, overline(x) in overline(B)_r (a)$, то $norm(G_y (x) - G_y (overline(x))) <= norm(x-overline(x))/2$

Проверим $y in B_R (b)$ Подберем такое $R > 0$, что $G_y: overline(B)_r (a) -> B_r (a)$

Возьмем $x in overline(B)_r (a), norm(G_y (x) - a) = norm(G_y (x) - G_y (a) + G_y (a) - a) <= underbrace(norm(G_y (x) - G_y (a)), norm(x-a)/2 <= r/2) + underbrace(norm(G_y (a) - a), A^(-1)(y-f(a)) = A^(-1)(y-b)) <= r/2 + norm(A^(-1) (y-b)) <= r/2 + norm(A^(-1)) (y-b) < r/2 + R norm(A^(-1)) < r$ выберем $R>0$, чтобы такое неравенство выполнялось

Следовательно $G_y : overline(B)_r (a) -> B_r (a)$ - сжатие с коэфф. $1/2$ если $y in B_R (a)$

Тогда у $G_y$ существует неподвижная точка $x_y$

$x_y = G_y (x_y) = x_y + A^(-1)(y- f(x_y)) => A^(-1) (y-f(x_y)) = 0 => y = f(x_y)$

$=> f(B_r (a)) supset B_R (b)$

$V:= B_R (b)$ и $U:= B_r (a) inter f^(-1) (V)$ $f^(-1)$ открыто, так как прообраз открытого

$=> f: U-> V$ биекция

Проверим, что обратное отображение непрерывно

$y, overline(y) in V, x in f^(-1)(y)$ и $overline(x) = f^(-1) (overline(y))$, тогда $G_y (x) = x$ и $G_overline(y) (overline(x)) = overline(x)$

$norm(x-overline(x)) <= 1/(1-1/2) dot norm(G_y (x) - G_overline(y) (x)) = 2 norm((x+A^(-1)(y-f(x))) - (x+ A^(-1) (overline(y) - f(x))) ) = 2 norm(A^(-1) (y-overline(y))) <= 2 norm(A^(-1)) norm(y-overline(y))$

$norm(f^(-1) (y) - f^(-1) (overline(y))) = norm(x-overline(x))$
]

#proof[Часть 2][
  Непрер. дифф $f^(-1)$

  $f(x+h) = f(x) + f'(x) dot h + alpha(h) dot norm(h), alpha(h) ->_(h->0) 0$

  $f'(x) =: T$

  $f(x) = y, k = f'(x)h + alpha(h) norm(h)$

  $f^(-1) (y + k) = x + h = f^(-1) (y) + h = f^(-1)(y) + T^(-1)k + o(norm(k)) => f^(-1)$ дифф. в точке $y$

  Надо понятЬ, что $h = (f'(x))^(-1)k + o(norm(h))$

  Знаем, что если $k-> 0$, то $h-> 0$ (это непрерывность $f^(-1)$)

  $norm(k) = norm(T h + alpha(h) norm(h)) >= norm(T h) - abs(alpha(h)) norm(h) >= norm(h)/norm(T^(-1)) - abs(alpha(h)) norm(h) = norm(h) (1/norm(T^(-1)) - abs(alpha(h)))> 0$ при малых $k$

  $h - T^(-1) k = h - T^(-1) (T h + alpha(h) norm(h)) = h - h - T^(-1) (alpha(h) norm(h)) = -norm(h) T^(-1) (alpha(h))$

  $norm(h - T^(-1)k) = norm(h) norm(T^(-1)(alpha(h))) <= norm(h) norm(T^(-1)) norm(alpha(h)) = o(norm(k))$ 
]

#corollary[
  $f: D -> RR^n$ непрерывна дифф и $f'(x)$ обратимо $forall x in D$

  $G subset D$ - открытое

  Тогда $f(G)$ - открытое
]

#proof[
  возьмем $b in f(G)$ хотим доказать, что она внутренняя 
  
  $=>$ найдется $a in G$, такая, что $b = f(a)$ и $f'(a)$ обратим

  $=>$ по теореме об обратной функции $exists U$ и $V$ окрестности точек $a$ и $b$, такие что $f: U -> V$ - биекция
  
  $=> V subset f(G)$, $b$ внутрення точка $f(G)$
]

#theorem[Утверждение][
  $A: RR^(n + m) -> RR^n$ линейное $RR^(n+m) = RR^n times RR^m, (a,b) a in RR^n, b in RR^m$

  Если из условия $A(h,0) = 0$ следует, что $h = 0$

  Тогда уравнение $A(x,y) = 0$ имеет единственное решение при любом фиксрованном $y subset RR^m$
]

#proof[
  $A(x,y) = 0, A(x,0) + A(0,y) = A(x,y)$

  $A(x,0) = - A(0,y), A(dot,0): RR^n -> RR^n$ линейное
]

#theorem[о неявной функции][
  $f: D -> RR^n, D$ открытое $(a,b) in D$

  $f$ непрерывно дифф и $A:= f'(a, b)$ удовлетворяла условию $A(h,0) = 0 => h =0$

  Тогда сущетсвуют $W subset RR^m$ окрестность точки $b$ и функция $g: W -> RR^n$, такая что $g(b) = a$ и $f(g(y),y) = 0 forall y in W$, причем функция $g$ будет непрерывно дифф.

  Такая функция $g$ единственна
]

#proof[
  Рассмотри функция $F(x,y) = (f(x,y), y)$ (по первым координатам это $f(x,y)$, по последним $y$)

  $F: D -> RR^(n+m)$

  $F(a,b) = (f(a,b), b) = (0,b)$

  $F' = mat(f'_x, f'_y;0, E)$ непрер. дифф $F'(a,b)$ обратимо?

  $det F'(a,b) = det f'_x (a,b)$

  $0 = (f'_x | f'_y)vec(h,0) = f'_x h => h =0$ то есть $det f'_x != 0$

  то есть выполнены условия Т. об обратной функции $=> exists U$ - окрестность $(a,b)$ и $V$ - окрестность точки $(0,b)$, т. ч. $F: U-> V$ биекция и $G:= F^(-1): V -> U$ непрер. дифф.

  $G(z,t) = (phi(z,t), psi(z,t)), (z,t) = F(G(z,t)) = F(phi(z,t), psi(z,t)) = (f(phi(z,t), psi(z,t)), psi(z,t)) => psi(z,t) = t => f(phi(z,t), t) = z$

  ${0} times W subset V, W$ - окрестность точки $b$

  $w in W, (0,w) subset V$ и его можно подставлять в формулу $f(phi(z,t),t) = z$

  тогда $f(phi(0,w),w) = 0$

  Берем $g(w):= phi(0,w)$

  $g(b) = phi(0,b) = a$

  $f(g(w),w) = 0$ и $g$ непрерывно дифф. так как $phi$ непрерывно дифф

  $f(x,y) = 0$ и $f(overline(x),y) = 0 => x = overline(x)$, так как $F(x,y) = (0,y) = F(overline(x),y)$, но $F$ - биекция, следовательно $x = overline(x)$ 
]