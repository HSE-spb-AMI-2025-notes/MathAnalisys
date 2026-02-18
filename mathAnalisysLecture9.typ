= Интегральное исчесление функций одной переменной
== Первообразная и неопределенный интеграл
=== Определение
$f: chevron a, b chevron.r -> RR, $ функция $F: chevron a, b chevron.r -> RR$, если $F`(x) = f(x) forall x in chevron a, b chevron.r$
=== Теорема
$f: chevron a, b chevron.r$ непрерывна на отрезке, то у $f$ есть первообразная
==== Доказательство
не сейчас
==== Замечание
не у всех функций есть первообразная. $f(x) = "sign" x$ \
Пусть $F$ первообразная $f$, тогда $F` = f$ принимает зачения ${-1, 0 , 1}$. Но по теореме Дарбу $F`$ должна приниматьвсе значения из $[-1, 1]$, противоречие
=== Теорема
Пусть есть $f, F: chevron a, b chevron.r -> RR$, $F$ первообразная $f$. Тогда 
1. $forall c in RR$ $F + c$ тоже первообразная $f$
2. Если есть другая первообразная $Phi: chevron a, b chevron.r -> RR$ тоже первообразная $f$, то $Phi - F = "const"$
==== Доказательство
1. $(F(x) + c)` = f(x)$ 
2. $(Phi(x) - F(x))` = f - f = 0 => Phi - F = "const"$
=== Определение
Неопределенный интеграл функции $f$ - множество всех ее первообразных\
Обозначение: $integral f = integral f(x) d x$ \
$F$ - первообразная $f$, $integral f(x) d x = {F(x) + C}$ (скобочки писать не будем (впадлу))
=== Таблица интегралов
+ $integral 0 d x = C$
+ $integral x^p d x = x^(p+1)/(p+1) + C, p != -1$
+ $integral (d x) / x = ln(abs(x)) + C$ \
+ $integral a^x d x = a^x/ln(a) + C, a!= 1, a > 0$
+ $integral sin x d x = - cos x + C$ \
+ $integral cos x d x = sin x + C$
+ $integral (d x)/(cos^2 x) = tg x + C$ \
+ котенганс очевидно
+ $integral (d x)/(1+x^2) = arctan x + C$ \
+ $integral (d x)/ (sqrt(1-x^2)) = arcsin(x) + C$ \
+ $integral (d x)/(1-x^2) = 1/2 ln(abs((1+x)/(1-x))) + C$ \
+ $integral (d x)/ sqrt(x^2 plus.minus 1) = ln abs(x + sqrt(x^2 plus.minus) 1) + C$
=== Проверка
3.
При $x > 0, (ln x)` = 1/x$. При $x < 0: (ln(abs(x)))` = (ln(-x))` = 1/x$ \
11.
$(1/2 ln abs((1+x)/(1-x)))` = 1/2((ln abs(1+x))` - (ln abs(1-x))`) = 1/2 (1/(1+x) + 1/(1-x)) = 1/(1-x^2)$
12.
$(ln abs(x + sqrt(x^2 + 1)))` = 1/(x + sqrt(x^2 + 1)) dot (x + sqrt(x^2 + 1))` = 1/(x+sqrt(x^2+1)) dot (1 + (2x)/(2sqrt(x^2+1))) = $ очев
=== Определение
$A, B$ - множества функция $chevron a, b chevron.r. A + B = {f + g, f in A, g in B}; c dot A = {c dot f | f in A}, A dot B = {f dot g | f in A, g in B}$ \
=== Теорема. арифметические действия с неопределенным интегралом
$f, g : chevron a, b chevron.r -> RR, f ,g$ - имеют первообразные \
$alpha, beta in RR$. Тогда: \
+ $f + g$ тоже имеют первообразную $integral f + g = integral f + integral g$ \
+ $alpha f$ имеет первообразную $integral alpha f = alpha integral f, alpha != 0$
+ $alpha f + beta g$ тоже имеет первообразную, $integral (alpha f + beta g) = alpha integral f + beta integral g$ при $abs(alpha) + abs(beta) != 0$ \
==== Доказательство
Пусть $F, G$ - первообразные $f, g$. Тогда $F + G$ - первообразыне для $f + g$ \
$integral (f + g) = F + G + C, integral f = F + C, integral g = G + C$ \
Остальное очев
=== Теорема (замена переменной в неопределенном интеграле)
$f : chevron a , b chevron.r -> RR, phi: chevron c, d chevron.r -> chevron a, b chevron.r$ - дифф. $F$ - первообразная $f$.
$integral f(phi(t)) phi`(t) d t = F(phi(t)) + C$\
==== Доказательство
Тривиальн
==== Следствие
$integral f( alpha x + beta) d x  = F(alpha x + beta)/alpha + C, alpha != 0.$ (Подставить $phi(x) = alpha x + beta$)
=== Теорема (формула интегрирования по частям)
$f, g in chevron a, b chevron.r -> RR$  и $f` g$ имеет первообразную, тогда $f g`$ тоже имеет первообразную и $integral f g` = f g - integral f` g$
==== Доказательство
$H$ - первообразная для $f` g$. $(?) f g$ - $H$ - первообразая для $f g`$ \
$(f g - H)` = f`g + f g` - H` = f g` qed$ \
= Площади и определенный интеграл
$cal(F)$ - множество всех ограниченных помножеств в плоскости
=== Определение
Квазиплощадь это отображение $sigma: cal(F) -> [0; + infinity)$, удовлетворяющее следующим свойствам:
+ $sigma (chevron a, b chevron.r times chevron c, d chevron.r) = (b-a)(d-c)$ \
+ $overline(E) subset E => sigma(overline(E)) <= sigma (E) $ \
+ Множество $E$ разделено вертикальной прямой $l$ на $E_-$ и $E_+$ $=> sigma(E) = sigma(E_-) + sigma(E_+)$ (точки $l$ могут принадлежать как $E_-$ и $E_+$)
==== Замечание
Логично требовать вместо условий 2 и 3 одно свойство условий $2`$: если $A inter B = emptyset$, то $sigma(A union B) = sigma(A) + sigma(B)$. Но существование такого объекто неочев (сложно)
=== Теорема
$sigma(E) = inf {sum_(k=1)^n abs(P_k) : union_(k=1)^n P_k supset E, P_k - "прямоугольник со сторонами || осям координат"}$ - квазиплощадь, не меняется при параллельном переносе \
апоЖ\
==== Доказательство
Проверим три свойства
+ Пусть $P = chevron a, b chevron.r times chevron c, d chevron.r (?) sigma(P) (b-a)(d-c)$ \ $<= {P}$ - покрытие $P$ $=> sigma (P) <= abs(P) = (b-a)(c-d)$ \ $>=$ Пусть $union_(k=1)^n P_k > P$ надо доказать, что $sum_(k=1)^n abs(P_k) >= abs(P)$ Продлим стороны $P_k$ и $P$, если мы посмотрим на каждый прямоугольник $P_k$, то он разбит на маленькие прямоугольники. $P$ тоже разбит на маленькие прямоугольники, все эти маленькие прямоугольники образуют покрытие $P$, $sum_(k=1)^n abs(P_k) >= sum abs("маленьких прямоугольников") >= sum abs("маленьких прямоугольников, входящих в " P) = abs(P)$ $qed$
+ любое покрытие $E$ - это покрытие $overline(E) => sigma(overline(E)) <= sigma(E)$
+ Пусть $E$ разделено вертикальной прямой $l$ на $E_-, E_+$. $(?) sigma(E) = sigma(E_-) + sigma(E_+)$ \ $<=$ Фиксируем $epsilon > 0$. Рассмотрим покрытие $union_(k=1)^m P_k^+ > E_+$, такое что $sum_(k=1)^m abs(P_k^+) <= sigma(E_+) + epsilon$ (по определению inf). Аналогично рассматриваем покрытие $union_(i=1)^n P_i^- > E_-$, такое что $sum_(i=1)^n abs(P_i^-) <= sigma(E_-) = epsilon$. $P_1^+, P_2^+, dots, P_m^+, P_1^-, P_2^-, dots P_n^-$ - образуют покрытие $E$, значит $sigma(E) <= sum_(k=1)^(m) abs(P_k^+) + sum_(i=1)^n abs(P_i^-) <= sigma(E_+) + epsilon + sigma(E_-) + epsilon = sigma(E_+) + sigma(E_-) + 2 epsilon$, устремим $epsilon$ к нулю. \
  $>=$ Пусть есть $P_1, dots P_n$ - покрытие $E$. Разделим каждый прямоугольник $P_k$ на $P_k^-$ и $P_k^+$ при помощи прямой $l$ (некоторые могут быть пустыми) \
  Тогда $P_1^+, dots P_n^+$ - покрытие $E_+$, а с минусами можно догадаться. Рассмотрим $sum_(k=1)^n abs(P_k) = sum_(k=1)^n abs(P_k^+) + sum_(k=1)^n (P_k^-) >= sigma(E_+) + sigma(E_-)$. Взяв inf по покрытиям множества $E$ получаем что хотели 
==== Замечания
+ Квазиплощадь неединственна. Пример: $sigma_1 (E) = inf{sum_(k=1)^oo abs(P_k)}$ \ Если $E = ([0,1] inter QQ) times([0,1] inter QQ) => sigma_1 (E) = 0$, но $sigma(E) = 1$
+ Парадокс Банаха-Тарского. Шар в $RR^3$ можно разделить на 5 непересекающихся частей, применить к каждой из частей движение (параллельный перенос и вращение) и получить два шара того же радиуса
+ Следующий семестр "правильное" понятие меры Лебега \
=== Определение
$f: [a,b ] -> RR$ непрерывная $, f_+max{f, 0}, f_+(x) = max{f(x), 0}, f_- = max{-f, 0}$
==== Свойства
+ $f_plus.minus >= 0$
+ $f = f_+ - f_-, abs(f) = f_+ + f_-$
+ $f_+ = (f + abs(f))/2, f_- = (abs(f) - f)/2$
+ Если $f$ была непрерывной,то $f_+$ и $f_-$ были непрерывны
=== Определение
$f: [a,b] -> RR. f>= 0,$ пографик $f$ - это $P_f := {(x,y) in RR^2, x in [a,b], 0 <= y <= f(x)}$ \
=== Определение
$f in C[a,b]. integral_a^b f = integral_a^b f(x) d x = sigma (P_f_+) - sigma (P_f_-)$
```
 /\_/\  
( o.o ) 
 > ^ < 
```
=== Свойства
+ $integral_a^a f = 0$

+ $integral_a^b 0 = 0$

+ $integral_a^b c = c(b-a)$

+ $integral_a^b (-f) = - integral_a^b f$ Доказательство: $(-f)_+ = max{-f, 0} = f_-, (-f)_- = max{(-f), 0} = f_+$,\ $integral_a^b (-f) = sigma(P_(-f)_+) - sigma(P_(-f)_-) = sigma(P_f_-) - sigma(P_f_+) = - integral_a^b f$

+ Если $f>= 0$, то $integral_a^b sigma(P_f)$ Доказательство: Если $f>=0$, то $f_+ = f, f_- = 0$

+ Если $f >= 0, f in C[a,b]$ и $integral_a^b f = 0$, то $f equiv 0$ Доказательство: Пусть $f equiv.not 0$. Найдется $x_0 in [a,b]$, для которой $f(x_0) > 0$. $epsilon:= f(x_0)/2$, найдется $delta > 0$, такое что при $x in (x_0 - delta, x_0 + delta): f(x) > f(x_0)/2 = f(x_0) - epsilon => P_f supset [x_0 - delta/2, x_0 +delta/2] times [0, f(x_0)/2]$ \ $integral_a^b f = sigma(P_f) >= sigma([x_0 - delta/2, x_0 + delta/2] times [0, f(x_0)/2]) > 0$
= Свойства определенного интеграла
== Теорема аддитивность
$f: [a,b] -> RR, c in (a,b)$ \ Тогда $integral_a^b f = integral_a^c f + integral_c^b f$
=== Обозначение $P_g ([alpha, beta]) := {(x,y): x in [alpha, beta], 0 <= y <= g(x)}$
=== Доказательство
$integral_a^b f = sigma(P_f_+ ([a,b])) - sigma(P_f_-([a,b])) = sigma(P_f_+([a, c])) + sigma(P_f_+([c,b])) - sigma(P_f_-([a,c])) - sigma(P_f_-([c, b])) = integral_a^c f + integral_c^b f$
=== Следствие
$f:[a,b] -> RR, a < c_1 < c_2 < dots < c_n < b$ Тогда $integral_a^b = integral_a^c_1 f + integral_(c_1)^c_2 f + dots + integral_(c_n)^b f$ (индукция)
== Теорема монотонность
$f, g: [a,b] -> RR, f(x) <= g(x) forall x in [a,b]$ \
Тогда $integral_a^b f <= integral_a^b g$
=== Доказательство
$f_+ = max{0, f} <= max{0, g} = g_+ => P_f_+ subset P_g_+$, аналогично $f_- = max {0, -f} >= max{0, -g} = g_- => P_f_- supset P_g_-$ \
$=> sigma(P_f_+) <= sigma(P_g_+), sigma(P_f_-) >= sigma (P_g_-) => integral_a^b f = sigma(P_f_+) - sigma(P_f_-) <= sigma(P_g_+) - sigma(P_g_-) = integral_a^b g$
=== Следствия \
==== 1.
$f in C[a,b]$ Тогда $(b- a) dot min_(x in [a,b]) f(x) <= integral_a^b f <= (b- a) max_(x in [a,b]) f(x)$
===== Доказательство
$A:= min f, B:= max f => A <= f(x) <= B forall x => A(b-a) = integral_a^b A <= integral_a^b f <= integral_a^b B = B(b-a)$
==== 2.
$abs(integral_a^b f) <= integral_a^b abs(f)$
===== Доказательство
$-abs(f) <= f <= abs(f) => -integral_a^b abs(f)  = integral_a^b -abs(f) <= integral_a^b f <= integral_a^b abs(f) => abs(integral_a^b f) <= integral_a^b abs(f)$
== Теорема о среднем 
$f in C[a,b]$ Тогда $exists c in [a,b]$, для которой $integral_a^b f = (b-a) f(c)$
=== Доказательство:
$min_(x in [a,b]) f(x) <= 1/(b-a) integral_a^b f <= max_(x in[a,b]) f(x)$. Но непрерывная функция принимает в качестве значений весь отрезок $[min f , max f]$, в частности у нее есть значение $1/(b-a) integral_a^b f$
== Определение
Среднее значение функции $f$ на отрезке $[a,b]$ это $1/(b-a) integral_a^b f$
== Определение интеграл с переменным верхним перделом
$f: [a,b] -> RR, Phi(x):= integral_a^x f, a<= x <= b$, замечание $Phi(a) = 0$ \
== Определение интеграл с переменным нижним перделом
$Psi(x):= integral_x^b f, a <= x <= b$ \
Замечание:
+ $Psi(x) = 0$
+ $Phi(x) + Psi(x) = integral_a^b (f)$

== Теорема Барроу
$f in C[a,b], Phi(x):= integral_a^x f$ \
Тогда $Phi`(x) = f(x)$
=== Доказательство
$Phi_+`(x) = lim_(y->x_+) (Phi(y) - Phi(x))/(y-x) = lim_(y->x_+) (integral_a^y f - integral_a^x f)/(y-x) = lim_(y-> x_+) 1/(y-x) integral_x^y f$ (посмотрим на это выражение и напишем теорему о средних) $= f(c_y), c_y in [x,y]$ то есть хотим посчитать предел $lim_(y->x_+) f(c_y) = f(x)$ \
Если $y_n$ убывает к $x$, то $c_y_n -> x =>$ по непрерывности $f$ получается, что $f(c_y_n) -> f(x)$\ 
Для $Phi_-`(x)$ аналогично 
=== Следствие 1
$f in C[a,b], Psi(x):= integral_x^b f => Psi`(x) = - f(x)$
==== Доказательство 
$A:= integral_a^b f => Psi(x) = A - Phi(x) => Psi`(x) = - Phi`(x) = -f(x)$
=== Следствие 2
$f in C chevron a, b chevron.r$, тогда у $f$ есть первообразная
==== Доказательство
Возьмем $c in (a,b)$
$F(x):= cases(Phi(x) "при " x >= c, -Psi(x) "при " x<= c)$
== Теорема (формула Ньютона-Лейбница)
$f in C[a,b], F$ - первообразная $f$ на $[a,b]$, тогда $integral_a^b f = F(b) - F(a)$
=== Доказательство
$Phi(x) := integral_a^x f$ - первообразная, $F$ - первообразная $=> Phi(x) = F(x) + C$, но $0 = Phi(a) = F(a) + C => C = -F(a) => Phi(x) = F(x) - F(a) => integral_a^b f = Phi(b) = F(b) - F(a)$
== Обозначение 
$F|_a^b := F(b) - F(a)$ - подстановка \
== Соглашение
Если $b < a integral_a^b f := - integral_b^a f$
== Теорема линейность интеграла
$f, g: [a,b] -> RR, alpha, beta in RR$\
Тогда $integral_a^b (alpha f + beta g) = alpha integral_a^b f + beta integral_a^b g$
=== Доказтельство
$F, G$ - первообразная для $f, g$ \
$alpha F + beta G$ - первообразная для $alpha f + beta g$ \ 
$(alpha F + beta G)` = alpha F` + beta G` = alpha f + beta g$ \ 
$=>^"Н.Л" integral_a^b(alpha f + beta g) = alpha F + beta G |_a^b = alpha dot F |_a^b + beta G |_a^b = alpha integral_a^b f + beta integral_a^b g$
== Теорема формула интегрирования по частяи
$f, g in C^1[a,b]$, тогда $integral_a^b f g` = f g |_a^b - integral_a^b f` g$
=== Доказательство
$H$ - первообразная для $f`g => f g - H$- первообразная для $f g`$ \
$(f g - H)`= (f g)` - H` = f`g + f g` - f`g = f g`$ \
$integral f g` = (f g - H) |_a^b = f g |_a^b - H|_a^b = f g |_a^b - integral_a^b f` g$
== Теорема замена переменной в определенном интеграле
$g in C[a,b], phi: [c,d] -> [a,b]$ $phi in C^1[a,b]$, $p, q in [c, d]$ \
Тогда $integral_p^q f(phi(t)) phi`(t) d t = integral_phi(p)^phi(q) f$
=== Доказательство
$F$ - первообразная $f$, $F circle.small phi$ - первообразная для $f(phi(t))phi`(t)$ \
$(F(phi(t)))` = F`(phi(t)) dot phi`(t) = f{phi(t)} phi`(t)$ \
$integral_phi(p)^phi(q) f = F(phi(q)) - F(phi(p)) = F circle.small phi |_a^b = integral_a^b f(phi(t))phi`(t) d t$ \ 
=== Пример
$integral_a^b (t/(1+t^4)) d t, phi(t) = t^2, phi`(t) = 2t, f(x) = 1/(1+x^2) $ \
$= 1/2 integral_a^b f(phi(t)) phi`(t) d t = 1/2 integral_(phi(a))^phi(b) f = 1/2 integral_(a^2)^(b^2) (d x)/(1+x^2) = 1/2 arctan |_(a^2)^(b^2)$
= Прододжение формулы интегрирования по частям
== Пример
$W_n := integral_0^(pi/2) cos^n x d x = integral_0^(pi/2) sin^n x d x$
$integral_0^(pi/2) cos^n x d x = integral_0^(pi /2) sin^n (pi/2 - x) d x | phi(x) := y = pi/2 - x | = - integral_(phi(0))^(phi(pi/2)) sin^n y d y = - integral_(pi/2)^0 sin^n y d y = integral_0^(pi/2) sin^n x d x$ \
$W_0 = pi/2$ \
$W_1 = integral_0^(pi/2) sin x d x = -cos |_0^(pi/2) = 1$ \
$w W_2 = integral_0^(pi/2) cos^2 + integral_0^(pi/2) sin^2 = integral_0^(pi/2) cos^2 + sin^2 = pi/2 => W_2 = pi/4$
$W_n = integral_0^(pi/2) sin^n x d x = - integral_0^(pi/2) sin^(n-1) x (cos x)` d x = -(underbrace(sin^(n-1) cos |_0^(pi/2), = 0) - integral_0^(pi/2) (n-1) sin^(n-2) x underbrace(cos x dot cos x, 1-sin^2x) d x ) = (n-1) (underbrace(integral_0^(pi/2) sin^(n-2) x d x, W_(n-2)) - integral_0^(pi/2) sin^n x d x) $ \
$W_n = (n-1)/n W_(n-2)$ \
$W_(2n) = (2n-1)/(2n) (2n-3)/(2n-2) dot dots dot 1/2(W_0 = pi/2) => W_(2n) = (2n-1)!!/(2n!!) dot pi/2$ \
$W_(2n+1) = (2n)/(2n+1) dot (2n-2)/(2n-1) dot dots dot 2/3 dot (W_1 = 1) => W_(2n+1) = (2n!!)/(2n+1)!!$
== Формула Валлиса
$lim (2n)!!/((2n-1)!!) dot 1/(sqrt(2n+1)) = sqrt(pi/2)$
=== Доказательство
на $[0, pi/2] sin^(2n) >= sin^(2n+1) >= sin^(2n+2)$ \
$integral_0^(pi/2) sin^(2n) >= integral_0^(pi/2) sin^(2n+1) >= integral_0^(pi/2) sin^(2n+2)$ \
$W_(2n) >= W_(2n+1) >= W_(2n+2)$ \
$pi/2 (2n-1)!!/(2n)!! >= (2n)!!/(2n+1)!! >= pi/2 (2n+1)!!/(2n+2)!! = pi/2 (2n-1)!!/(2n)!! dot (2n+1)/(2n+2)$ \
$pi/2 >= (2n)!!/(2n+1)!! dot (2n)!!/(2n-1)!! >= pi/2 (2n+1)/(2n+2) -> pi/2$ \
$((2n)!!/(2n-1)!!)^2 dot 1/(2n+1) -> pi/2$
== Следствие
$C_(2n)^n tilde 4^n/sqrt(pi n)$ \
=== Доказательство
$C_(2n)^n = (2n)!/(n!)^2 = ((2n)!! (2n-1)!!)/(n! dot n!)$ \
$(2n)!! = 2 dot 4 dot 6 dot dots dot 2n = 2^n dot 1 dot 2 dot 3 dot dots dot n = 2^n dot n!$ \

$(C_(2n)^n)/4^n = ((2n)!! (2n-1)!!)/(2^n (n!) dot 2^n n!) = (2n-1)!!/(2n)!!$ \

Формула Валлиса $(2n-1)!!/(2n)!! dot sqrt(2n+1) -> sqrt(2/pi)$ \
$(2n+1)!!/(2n)!! tilde sqrt(2/pi) dot 1/(sqrt(2n+1)) tilde sqrt(2/pi) dot 1/(sqrt(2n)) = 1/sqrt(pi n)$

== Формула Тейлора с остатком в интегральной форме
$f: chevron a, b chevron.r -> RR, f in C^(n+1) chevron a , b chevron.r, x_0, x in chevron a, b chevron.r$ \
Тогда $f(x) = sum_(k=0)^n (f^((k))(x_0))/(k!) (x-x_0)^k + 1/n! integral_(x_0)^x f^((n+1)) (t) (x-t)^n d t$
=== Доказательство
Индкукция по $n$ \
База $n = 0$ \
$f(x) = f(x_0) + 1/0! integral_(x_0)^x f`(t) d t = f(x_0) +f(x) - f(x_0)$ \
Переход $n -> n+1$ \
$f(x) = sum_(k=0)^n (f^((k)) (x_0))/k (x-x_0)^k + 1/n! underbrace(integral_(x_0)^x f^((n+1)) (t) (x-t)^n d t, I:= )$ \
$I = $ \
$u = f^((n+1)), u` = f^((n+2)), v = (x-t)^n, v` = -(x-t)^n/(n+1)$ \
$I = integral_(x_0)^x u v` = u v |_(x_0)^x - integral_(x_0)^(x) u` v = underbrace(-(f^((n+1)) (t))/(n+1) (x-t)^(n+1)|_(t=x_0)^(t=x), (f^((n+1))(x_0))/(n+1) dot (x-x_0)^(n+1)) + integral_(x_0)^x (f^((n+2)) (t))/(n+1) (x-t)^((n+1)) d t$ \
$f(x) = (f^((n+1)) (x_0))/(n+1)! (x-x_0)^(n+1) + 1/(n+1)! integral_(x_0)^x f^((n+2))(t) (x-t)^(n+1) d t$
=== Пример
$H_j := 1/j! integral_0^(pi/2) ((pi/2)^2 - x^2)^j cos x d x$ \
Наблюдение: эта штука точно положительна, значит интегральчик точно положительный
Свойтсва:
+ $0 < H_j <= 1/j!, integral_0^(pi/2) (pi/2)^(2j) cos x d x = (pi/2)^(2j)/j!$
+ Если $c in RR$, то $c^j H_j -> 0$, так как $0 <= abs(c^j H_j) <= (abs(c) pi^2/4)^j/j! ->_(j->oo) 0$
+ $H_0 = 1, H_1 = 2$
+ $H_j = (4j - 2)H_(j-1) -pi^2 H_(j-2)$, при $j>=2$ \ Доказательство: $j! H_j = integral_0^(pi/2) ((pi/2)^2 -x^2)^j cos x d x $ \ $u = ((pi/2)^2 -x^2)^j, v` = cos x, u` = - 2x j ((pi/2)^2 - x^2)^((j-1)), v = sin x$ \ $underbrace(((pi/2)^2 - x^2)^j sin x |_(x=0)^(x=pi/2), =0 ) + 2j integral_0^(pi/2) x ((pi/2)^2 - x^2)^(j-1) sin x d x$ \ $u = x ((pi/2)^2 - x^2)^(j-1), v` = sin x, v = -cos x, u` = ((pi/2)^2 - x^2)^(j-1) - 2 (j-1)x^2((pi/2)^2 - x^2)^(j-2) =, x = (pi/2)^2 - ((pi/2)^2 -x^2), = ((pi/2)^2 - x^2)^(j-1) - 2(j-1) (pi/2)^2 ((pi/2)^2 - x^2)^(j-2) + 2(j-1) ((pi/2)^2 -x^2)^(j-1)$ \ подставляем в изначальный интеграл: \ $= 2j (x((pi/2)^2 -x^2)^(j-1) (-cos x)|_(x=0)^(x=pi/2) +  (2j - 1) integral_(0)^(pi/2) ((pi/2)^2 - x^2)^(j-1) cos x d x - (pi^2/4) 2(j-1) integral_0^(pi/2) ((pi/2)^2 - x^2)^(j-2) cos x d x ) = j!$ \ $j! H_j = 2j (2j - 1) (j-1)! H_(j-1) -2j pi^2/4  2 (j-1) (j-2)! H_(j-2)$ \ $H_j = 2 (2j- 1) H_(j-1) - pi^2 H_(j-2)$ 
== Теорема Ламберта 
$pi$ и $pi^2$ - иррациональное число \
=== Доказательство
От противного. Предположим, что $pi^2 = m/n$, где $m, n in NN$ \
Проверим, что тогда $n^j H_j$ - целое число По индукции по $j$. База $j = 0, j = 1$ очевидный \ Переход $j-2, j - 1 -> j$ \
$n^j H_j = underbrace((4j - 2) dot n, "целое") dot n^(j-1) H_j-1 - underbrace(n^2 pi^2, =m^2 n "целое") n^(j-2) H_(j-2)$ - индукционное предположение \
Понимаем, что $n^j H_j$ - целоеб $n^j H_j > 0$ $=>$ - $n^j H_j >= 1$, с другой стороны, если воспользуемся свойством номер 2 $n^j H_j ->_(j->oo) 0$, противоречие :(
= Интегральные суммы
== Определение равномерно непрерывной функции
$f: E -> RR$ равномерно непрерывна, если $forall " " epsilon > 0 " " exists delta > 0: forall x, y in E, "т.ч" abs(x-y) < delta => abs(f(x) - f(y)) < epsilon $ \
=== Замечание
$f$ непрерывна во всех точках из $E$ означает, что $forall y in E " " forall epsilon > 0 " " exists delta > 0, forall x in E, "т.ч" abs(x-y) < delta => abs(f(x) - f(y)) < epsilon$
=== Примеры
1. $sin$ и $cos$ равномерно непрерывны на $RR$, $abs(sin x - sin y) <= abs(x - y) => delta = epsilon$ подходит \
2. $f(x) = x^2$ не равномерно непрерынвая на $RR$ \ Возьмем $epsilon = 1: $ Проверим, что никакое $delta > 0$ не подходит $f(x + delta/2) - f(x) = (x+delta/2)^2 - x^2 = x dot delta + delta^2/4 > x dot delta$ для $x = 1/delta$ все плохо \ $f(1/delta + delta/2) - f(1/delta) > 1$
3. $f(x) = 1/x$ не является равномерно непрерывной на $(0,1]$ \ Возьмем $epsilon = 1$ Проверим, что никакое $0 < delta < 1$, $x = delta/2, y = delta, f(x) - f(y) = 2/delta - 1/delta = 1/delta > 1$ \
== Определение
$f: E -> RR$ липшицева с константой $M$, если $forall x, y in E$ $abs(f(x) - f(y)) <= M abs(x - y)$ \
=== Замечание
+ липшицевость $=>$ равномерно непрерывна (просто берем в качестве $delta = epsilon/M$)
+ Если $f: chevron a, b chevron.r -> RR$ дифференцируема и $abs(f`) <= M$ на $chevron a, b chevron.r$, то $f$ липшицева с константой $M$ и, в частонсти, равномерно непрерывна 
== Теорема Кантора 
Непрерывная на отрезке функция равномерно непрерывна
=== Доказательство
$f: [a,b] -> RR$
Возьмем $epsilon > 0$, предположим, что никакое $delta$ для него не подходит  \
$delta = 1$ не подходит, значит найдутся такие точки $x_1, y_1 in [a,b]$, такое что $abs(x_1 - y_1) < 1,$ но при этом $abs(f(x_1) - f(y_1)) >= epsilon$  \
$delta = 1/2$ не подходит, значит найдутс такие точки $x_2, y_2 in [a,b]$, такое что $abs(x_1 - y_1) < 1/2$ и $abs(f(x_2) - f(y_2)) >= epsilon$ \
$dots$ \
$delta = 1/n$ не подходит $=>$ найдутся $x_n, y_n in [a,b]$, такие что $abs(x_n - y_n) < 1/n$ и $abs(f(x_n) - f(y_n))>= epsilon$ \
$y_n in [a,b]$ ограничена, последовательность по Т. Б-В выберем подпоследовательность $y_n_k -> c in [a,b]$ \ $abs(x_n - y_n) < 1/n => lim (x_n - y_n) = 0 => lim x_n_k = lim y_n_k + lim(x_n_k - y_n_k) = c + 0 = c$ \ $f$ непрерывна в $c$ означает, что $lim f(x_n_k) = f(c)$, аналогично $f(y_n_k) = f(c)$, тогда пердел разности $lim(f(x_n_k) - f(y_n_k)) = 0$, но с другой стороны $abs(f(x_n_k) - f(y_n_k)) >= epsilon$ противоречие, значит предположение не верно и какое-то $delta$ подойдет
== Определение
$f: E -> RR$ модуль непрерывности $omega_f (delta), delta > 0, omega_f (delta) := sup {abs(f(x) - f(y)) : x, y in E and abs(x - y) <= delta}$ 
=== Свойства
+ $omega_f (0) = 0$ и $omega_f (delta) >= 0$ 
+ $omega_f$ нестрого возрастает 
+ $omega_f (abs(x-y)) >= abs(f(x) - f(y))$
+ Если $f$ липшицева с константой $M$, то $omega_f (delta) <= M dot delta$ $abs(f(x) - f(y)) <= M abs(x -y) <= M dot delta$ 
+ $f: E -> RR$, тогда $f$ равномерно непрерывна на $E$ $<=> lim_(delta-> 0+) omega_f (delta) = omega_f (0) = 0$ \ Доказательство: \ $=>$ $forall epsilon > 0 " " exists delta >0 " " forall x, y in E and abs(x-y) < delta => abs(f(x) - f(y)) < epsilon$, тогда если $abs(x-y) <= delta/2 < delta$, тогда $abs(f(x) - f(y)) < epsilon => omega_f (delta/2) = sup{ abs(f(x) - f(y)) : abs(x-y) <= delta/2}$  \ Следовательно, при $0 <= t <= delta/2 " " 0 <= omega_f (t) <=  omega_f (delta/2) <= epsilon => lim_(t-> 0+) w_f (t) = 0$ \ $arrow.l.double$ $lim_(delta -> 0+) omega_f(delta) = 0$ по $epsilon > 0$ выберем такое $delta > 0$, что $omega_f (delta) < epsilon$ \ $abs(f(x) - f(y)) <= omega_f (delta) < epsilon$ (если $abs(x-y) < delta$) $=> f$ равномерно непрерывна 
+ Если $f : [a,b] -> RR$ и непрерывна, то $lim_(delta -> 0+) w_f (delta) = 0$ Доказательство: Кантора и свойство 5
== Определение Дробление отрезка (разбиение, пунктир) 
Такой набор точек $a = x_0 < x_1 < x_2 < dots < x_(n-1) < x_n = b$ \
Будем обозначать $tau = {x_0, x_1, dots, x_n}$ \
Мелкость (ранг) дробления  \
$abs(tau) = max {x_1 - x_0, x_2 - x_1, dots , x_n - x_(n-1)}$ - длина самого большого отрезка из нарезки \ 
Оснащение дробления - набор точки $xi_1, xi_2, dots xi_n$ такое что $xi_k in [x_(k-1), x_k]$
== Определение Сумма Римана (интегральная сумма)
$f: [a,b] -> RR$ $tau$ - его дробление, $xi$ - оснащение этого дробления $S(f, tau, xi) = sum_(k=1)^n f(xi_k) (x_k - x_(k-1))$
== Теорема об интегральной сумме 
$f in C[a,b]$, тогда $Delta := abs(integral_a^b f - S(f, tau, xi)) <=(b-a) omega_f (abs(tau))$ \
=== Доказательство
$integral_a^b f - S(f, tau, xi) = integral_a^b f - sum_(k=1)^n f(xi_k) (x_k - x_(k-1)) = sum_(k=1)^n integral_(x_(k-1))^(x_k) f - sum_(k=1)^n f(xi_k) (x_k - x_(k-1)) = sum_(k=1)^n integral_(x_(k-1))^x_k (f_t - f(xi_k)) d t$ \
$Delta <= sum_(k=1)^n integral_(x_(k-1))^x_k abs(f(t) - f(xi_k)) d t <= sum_(k=1)^n integral_(x_(k-1))^x_k omega_f (abs(tau)) d t = integral_a^b omega_f (abs(tau)) d t = omega_f (abs(tau)) (b-a)$ \ 
$abs(t - xi_k) <= x_k - x_(k-1) <= abs(tau) => abs(f(t) - f(xi_k)) <= omega_f (abs(tau))$

=== Следствие
$f in C[a,b]$ Тогда \
$forall epsilon > 0 " " exists delta > 0 " " forall$ дробления $tau$ мелкости $< delta$ и $forall$ его оснащения $abs(integral_a^b f - S(f, tau, xi)) < epsilon$ \
=== Следствие 
$f in C[a,b]$ и $tau_n$ - последовательность дроблений, такая что $tau_n$ стремиться к $0$ \ Тогда $forall xi_n$ - оснащение дроблений $tau_n$ $S(f, tau_n, xi_n) -> integral_a^b f$

=== Пример
$S_p (n) := 1^p + 2^p + dots + n^p, p > 0$ \
$lim_(n-> oo) (S_p (n))/(n^(p+1))$ \
Рассмотрим функцию $f(x) = x^p$ на $[0,1]$ - непрерывная функция \
дробление $[0,1]$ на равные отрезки $x_k = k/n = xi_k$ \
$S(f, tau, xi) = sum_(k=1)^n underbrace(f(k/n), (k/n)^p ) overbrace((k/n - (k-1)/n) = 1/(n^(p+1)), 1/n ) dot sum_(k=1)^n k^p = (S_p (n))/(n^(p+1))$\
Вывод $S_p (n) tilde (n^(p+1))/(p+1)$

== Определение
$f: [a,b] -> RR$ интегрируема по Риману на отрезке $[a,b]$, и $I in RR$ ее интеграл, если $forall epsilon > 0: exists delta > 0: forall tau$ - дробления $[a,b]$ и мелкости $< delta$ и $forall$ его оснащения $xi: abs(S(f,tau,xi)  - I) < epsilon$ \
=== Замечание
Если $f in C[a,b]$, то она интегрируема по Риману

== Лемма
$f in C^2[alpha, beta]$, тогда $integral_alpha^beta f - (beta - alpha) dot (f(alpha) - f(beta))/2 = -integral_alpha^beta f(x)`` (beta - x) (x - alpha) d x$
=== Доказательство
$gamma:= (alpha + beta)/2$
$integral_alpha^beta f(x) d x = integral_alpha^beta f(x) (x-gamma)` d x = f(x)(x-gamma)|_(x=alpha)^(x=beta) - integral_alpha^beta f`(x)(x-gamma) d x$ \

$f(x)(x-gamma)|_(x=alpha)^(x=beta) f(beta)(beta-gamma) - f(alpha)(alpha-gamma) = (f(alpha) + f(beta))/2 dot (beta-alpha)$ \
$Delta | y = f`, v = 1/2(beta-x)(x-alpha), v = 1/2(-alpha beta +(alpha +beta)x - x^2), v` = -x + (alpha+beta)/2 = gamma - x |= -integral_alpha^beta f`(x)(x-gamma) d x = underbrace(1/2 f`(x)(beta-x)(x-alpha) |_(x=alpha)^(x=beta), =0) - 1/2 integral_alpha^beta f``(x) (beta-x)(x-alpha) d x$

== Теорема оценка погрешности в форме трапеций
$f in C^2[a,b]$ $t$ - дробление отрезка $[a,b]$. Тогда $underbrace(abs(integral_a^b f - sum_(k=1)^n (x_k - x_(k-1) )(f(x_k)+f(x_(k+1)))/2), Delta := )<= 1/8 dot abs(tau)^2 dot integral_a^b abs(f``)$

=== Доказательство
$Delta = sum_(k=1)^n integral_(x_(k-1))^(x_k) f - sum_(k=1)^n (x_k - x_(k-1)) (f(x_k) + f(x_(k-1)))/2 = - 1/2 sum_(k=1)^n integral_(x_(k-1))^(x_k) f``(x) (x_k - x) (x-x_(k-1)) d x$ \
$abs(Delta) <= 1/2 sum_(k=1)^n abs(f``(x)) (x_k -x) (x-x_(k-1)) d x <= abs(tau)^2/8 sum_(k=1)^n integral_(x_(k-1))^(x_k) abs(f``) = abs(tau)^2/8 integral_a^b abs(f``)$ \
$(x_k - x) (x-x_(k-1)) <= (((x_k-x) + (x-x_(k-1)))/2)^2 = (((x_k - x_(k-1)))/2)^2 <= abs(tau)/4$

=== Замечание
1. Если дробление на равные отрезки, тогда $x_k = a + k/n (b-a) (x_k - x_(k-1) = (b-a)/n)$ и сумма площадей трапеций $= sum_(k=1)^n (b-a)/n dot (f(x_k) + f(x_(k-1)))/2 = (b-a)/n dot ((f(a) + f(b))/2 + sum_(k=1)^n f(x_k) )$ и в этом случае теорема дает $abs(Delta) <= (b-a)^2/(8n^2) integral_a^b abs(f``) = O(1/n^2)$
2. Как выглядит сумма Римана с равноотстоящими узлами и оснащением в правых концах $S(f, tau, xi) = sum_(k=1)^n f(x_k)(x_k - x_(k-1)) = (b-a)/n sum_(k=1)^n f(x_k)$ \ если $abs(f`) <= M, omega_f (delta) <= M delta$ \ $abs(S(f, tau, xi) - integral_a^b f) <= (b-a) omega_f ((b-a)/n) <= M(b-a)^2/n = O(1/n)$

== Теорема (формула Эйлера-Маклорена для второй производной)
$f in C^2(m,n), m,n in ZZ, sum_(k=m)^n f(k) = (f(m) + f(n))/2 + integral_m^n f + 1/2 integral_m^n f``(t) {t} (1-{t}) d t$
=== Доказательство
1.
$integral_(k-1)^k f = (f(k)+f(k-1))/2 - 1/2 integral_(k-1)^k f``(t)(k-t)(1-(k-1)) d t = (f(k) + f(k-1))/2 - 1/2 integral_(k-1)^k f``(t) {t} (1-{t}) d t$ \
$underbrace(sum_(k=m+1)^n integral_(k-1)^k f, integral_m^n f) = underbrace(sum_(k=m+1)^n (f(k) + f(k-1))/2, =sum_(k=m)^n f(k) -(f(m)+f(n))/2 ) - underbrace(1/2 sum_(k=m+1)^n integral_(k-1)^k f``(t){t}(1-{t}) d t, =integral_m^n f``(t) {t}(1-{t}) d t)$ \
== Примеры
$S_p (n):= 1^p + 2^p + dots + n^p, p>-1$ \
$f(x) = x^p, m = 1, f``(x) = p(p-1)x^(p-2)$ \
$S_p (n) = (1^p + n^p)/2 + underbrace(integral_1^n x^p d x, =(x^(p+1))/(p+1) |_1^n = (n^(p+1)-1)/(p+1) )  + 1/2 integral_1^n p (p-1) x^(p-2) {x}(1-{x}) d x$ \
$abs(S_p (n) - n^(p+1)/(p+1) -n^p/2 -1/2 +1/(p+1) ) <= (abs(p)abs(p-1))/2 integral_1^n x^(p-2) overbrace({x}(1-{x}),<= 1/2) d x <= (abs(p)abs(p-1))/8 integral_1^n x^(p-1) d x = (abs(p)abs(n^(p-1)-1))/8$\
$p+1 integral_1^n x^(p-2) d x = x^(p-1)/(p-1) |_(x=1)^(x=n) = (n^(p-1)-1)/(p-1)$ \
Случай $p in (-1, 1)$ \
$S_p (n) = n^(p+1)/(p+1) + n^p/2 + O(1)$ \
Случай $p > 1$ \
$S_p (n) = n^(p+1)/(p+1) + n^p/2 + O(n^(p-1))$ \
2.
Гармонические числа 

$H_n := 1 + 1/2 + 1/3 + dots + 1/n$ \
$f(x) = 1/x, m = 1, f`` = 2/x^3$ \
$H_n = (1+1/n)/2 + underbrace(integral_1^n (d x)/x, ln x |_1^n = ln n) + underbrace(integral_1^n ({x}(1-{x}))/(x^3) d x, a_n:=) = ln n + 1/2 +1/(2n) + a_n = ln n + (1/2 + a) + o(1)$ \
$a_(n+1) = a_n + underbrace(integral_n^(n+1) ({x}(1-{x}))/x^3 d x, >0) => a_(n+1) > a_n$ \
Проверим ограниченность $a_n <= integral_1^n (1/4)/x^3 d x= -1/8 dot (1/x^2) |_(x=1)^n = 1/8 - 1/(8n^2) <= 1/8$. значит ашки ограничены и существует пердел \
$a = lim a_n <= 1/8 => a_n = a + o(1)$ \
$1/2 + a = gamma$ - постоянная эйлера
== Упражнение
Доказать, что $H_n = ln n + gamma + 1/(2n) + O(1/n^2)$ (указание $integral_1^n = integral_1^(+oo) - integral_n^(+oo)$)
3. Формула Стирлинга
$ln n! = sum_(k=1)^n ln k$ \
$f(x) = ln x, m = 1, f``(x) = -1/x^2$ \
$ln n! = (ln 1 + ln n)/2 + integral_1^n ln x d x - underbrace(integral_1^n ({x}(1-{x}))/x^2 d x, b_n :=)$ \
$integral_1^n ln x d x = n ln n - n + 1$ \
$b_(n+1) > b_n$ и $0 < b_n < integral_1^n (1/4)/(x^2) d x = - 1/(4x) |_1^n = 1/4 - 1/(4n) < 1/4$, тогда существует предел $lim b_n =: b$ и $b_n = b + o(1)$ \
$ln n! = n ln n - n + 1/2 ln n + (1-b) + o(1)$ при $n-> oo$ \
$n! = n^n e^(-n) sqrt(n) e^(1-b)underbrace(e^(o(1)), 1+o(1) ) = n^n e^n sqrt(n) C(1+o(1)) tilde C n^n e^(-n) sqrt(n)$ \
Найдем $C$ \
$ 4^n/(sqrt(pi n)) tilde C_(2n)^n = (2n)!/(n!)^2 tilde (C(2n)^(2n) e^(-2n) sqrt(2n))/(C n^n e^(-n) sqrt(n))^2 = (C dot 2^(2n) sqrt(2n))/(C^2 sqrt(n) sqrt(n))$ \
$4^n/sqrt(pi n) tilde (2^(2n) sqrt(2))/(C sqrt(n)) => C equiv (2^(2n) sqrt(n))/(sqrt(n)) dot sqrt(pi n)/4^n = sqrt(2 pi) => C = sqrt(2 pi)$ \
Формула Стирлинга $n! equiv n^n e^(-n) sqrt(2 pi n)$ \
== Упражнение
Доказать, что $n! = n^n e^(-n) sqrt(2 pi n) (1 + O(1/n))$
= Несобственные интегралы
== Определение
$-oo < a < b <= +oo, f in C[a,b)$ \
Если существует $lim_(B->b-) integral_a^B f$, то он называется несобственный интегралом $integral_a^(->b) f$ \
$integral_a^(->b) f := lim_(B->b-) integral_a^B f$ 
== Определение
аналогично для предела справа
== Определение
Несобственный интеграл $integral_(->a)^b$ или $integral_a^(->b)$ называется сходящися, если соответствующий предел существуеют и конечен, в противном случае расходящийся
== Замечание
Если $f in C[a,b]$, то $integral_a^(->b) f = integral_a^b f$ \
$abs(integral_a^b f - integral_a^B f) = abs(integral_B^b f) <= integral_B^b abs(f) <= integral_B^b M = (b-B) dot M ->_(B->b-) 0$ \
== Примеры 1
$integral_1^(+oo) (d x)/x^p = lim_(y->+oo) integral_1^y (d x)/x^p = 1/(p-1) - lim_(y->+oo) 1/((p-1)y^(p-1)) = 0$ при $p>1$ и $-oo$ при $p<1$ \
Если $p != 1$, то $integral_1^y (d x)/x^p = -1/x^(p-1) dot 1/(p-1) |_(x=1)^(x=y) = 1/(p-1) - 1/((p-1) y^(p-1))$ \
То есть интеграл сходится при $p>1$ и равен $1/(p-1)$ и расходится при $p<1$ \
Если $p=1$ $integral_1^(+oo) (d x)/x = lim_(y->+oo) integral_1^y (d x)/x = lim_(y->+oo) ln y = + oo$ \
2.
$integral_0^1 (d x)/x^p = lim_(y->0+) integral_y^1 (d x)/x^p =_(p!=1) 1/(1-p) - lim_(y->0+) 1/((1-p) y^(p-1))$ этот предел $=0$ при $p < 1$ и $-oo$ при $p>1$ \
$integral_0^1 (d x)/x = lim_(y->+oo) integral_y^1 (d x)/x = lim_(y->0+) ln x |_y^1 = - lim_(y->0+) ln y = + oo$ \
при $p < 1$ интеграл сходится и равен $1/(1-p)$ \
при $p>= 1$ интеграл расходится и равен $+oo$
== Критерий Коши 
$f in C[a, b)$ и следующие условия равносильны: 
1. $integral_a^(-> b)$ сходится
2. $forall epsilon > 0: exists c in (a,b): forall A, B in (c, b)  abs(integral_A^B f) < epsilon$
Симметрично для нижнего 
=== Доказательство
$F(y):= integral_a^y f$ \
$integral_a^(->b) f$ - сходится $<=> lim_(y->b-) F(y)$ существует и конечен $<=>$(критерий Коши для $F$)  \
$b = +oo$ $forall epsilon > 0: exists E: forall A, B > E => abs(F(B) - F(A)) < epsilon, F(B) - F(A) = integral_A^B f$ \
$b < + oo$ $forall epsilon > 0: exists delta > 0: forall A, B in (b-delta, b) => abs(F(B) - F(A)) < epsilon$ \
В первом случае $c$ это $E$, во втором $b-delta$ это $c$
==== Замечение
$integral_a^b$ сходится $<=>$ существует $lim_(B->b-) F(B) - F(a)$, где $F$ - первообразная $f$ и $integral_a^(->b) f = lim_(B->b-) F(B) - F(a)$ \
$integral_a^(->b) f = lim_(B-> b-) integral_a^B f = lim_(B->b-) (F(B) - F(a))$ \
== Свойства несобственных интегралов
1. Аддитивность $f in C[a,b), c in (a,b)$ Тогда $integral_a^(->b) f$ - сходится $<=> integral_c^(->b) f$ сходится и в этом случае есть формула $integral_a^(->b) f = integral_a^c f + integral_c^(->b)f$ \ Доказательство $F$ - первообразная $f$. Тогда $integral_a^(->b) f$  сходится $<=>$ существует конечный $lim_(B->b-) F(B) <=> integral_c^(->b) f$ - сходится. \ $integral_a^(->b) = lim_(B->b-) F(B) - F(a) = lim_(B->b-) F(B) - F(c) + (F(c) - F(a))$
2. Если $integral_a^(->b) f$ сходится, то $lim_(y->b-) integral_y^(->b) f = 0$ \ Доказательство $integral_a^(->b) f = integral_1^(y) + integral_y^(->b) f$ \
3. Линейность $f, g in C[a,b), alpha, beta in RR$. Тогда $integral_a^(->b) (alpha f + beta g) = alpha integral_a^(->b) f + beta integral_a^(->b) g$ \ Доказательство $F, G$ - первообразные $f, g$ \ $integral_a^(->b) f = lim_(y->b-) F(y) - F(a)$ и $integral_a^(->b) g = lim_(y->b-) G(y) - G(a)$ \ $alpha integral_a^(->b) f + beta integral_a^(->b) g = lim_(y->b-) (alpha F(y) + beta G(y)) - (alpha F(a) + beta G(a)) = integral_a^(->b) (alpha f + beta g)$ \
==== Замечание
Если $integral_a^(->b) f$ сходится, а $integral_a^(->b) g$ расходится, то $integral_a^(->b) (f+g)$ расходится, от противного $g = (f + g) - f$

== Монотонность
$f, g in C[a,b)$ и $f <= g $ на $[a,b)$ \
Тогда $integral_a^(->b) f <= integral_a^(->b) g$ если эти несобственные интегралы определены \
=== Доказательство
$integral_a^y <= f_a^y g$ при $a < y < b$ \
$integral_a^b f <= integral_a^b g$ и предельный переход в неравенстве
== Формула интеграрования по частям
$f, g in C^1 [a,b)$ \
Тогда $integral_a^(->b) f g` = f g |_a^b - integral_a^(->b) f` g$ \
(если существуют 2 из трех пределов, то существует третий и верно равенство) \
=== Доказательство
$integral_a^y f g` = f g |_a^y - integral_a^y f` g$ при $a < y < b$ \
== Теорема  (формула замены переменной в несобственном интеграле)
$phi : [alpha, beta) -> [a,b), phi in C^1 [alpha, beta), f in C[a,b)$, $c:= lim_(gamma -> beta-) phi(gamma)$ \
Тогда $integral_alpha^beta f(phi(t)) phi`(t) d t = integral_phi(alpha)^c f(x) d x$  (если один из двух интегралов существует, то существует второй и они равны)
=== Доказательство
$F(y):= integral_(phi(alpha))^y f(x) d x, Phi(gamma) := integral_alpha^gamma f(phi(t)) phi`(t) d t$ \
$Phi(gamma) = F (phi(gamma))$
==== Простой случай (1 существует)
то есть существует $lim_(y->c-) F(y)$ \
Возьмем $gamma_n $ возрастает к $beta, Phi(y_n) = F(phi(gamma_n)) -> lim_(y->c-) F(y) = integral_phi(alpha)^c f(x) d x$ \
$phi(gamma_n) -> c$ из определения по Гейне (x) \
$Phi(gamma_n) = F(phi(gamma_n)) -> lim_(y->c-) F(y) = integral_phi(alpha)^c f(x) d x$ \
то есть поняли, что $lim_(gamma -> beta-) Phi(gamma)$ существует и равен $integral_phi(x)^c f(x) d x$ \
==== Сложный случай (2 существует)
то есть $lim_(gamma -> beta-) Phi(gamma)$ \
Если $c < b$, то тогда существует и 1. т.к. $f$ непрерывна на $[phi(alpha),c]$ \
Можно считать, что $c=b$ \
Возьмем какую-нибудь последовательность $b_n$ возрастающую и стремащуюся $b$ \
Хотим доказать, что $lim F(b_n)$ существует \
между $b_n$ и $b$ есть значения $phi$ в некоторых точках $phi(beta_n)$ \
$phi(alpha) < b_n phi(beta_n) => phi$ принимает значение $b_n$ в некоторых точках, лежащей между $alpha$ и $beta_n$ назовем это точку $gamma_n$ \
$b_n = phi(gamma_n), F(b_n) = F(phi(gamma_n)) = Phi(gamma_n)$ \
Осталось проверить, что $gamma_n -> beta$ От противного. Пусть нет стремления (это апатия) возьмем подпоследовательность $gamma_n_k -> beta_* < beta => phi(gamma_n_k) -> phi(beta_*)$, так как $phi$ непрерывна в $beta_*$, но $phi(gamma_n_k) = b_n_k -> b$, но $phi(beta_*) < b$ противоречие \
$F(b_n) = Phi(gamma_n) -> 2$
=== Замечание
$a < b < +oo, f in C[a,b)$ \
$integral_a^b f(x) d x$ \
$phi(t) = b - 1/t, lim_(t->+oo) phi(t) = b$ \
$phi(1/(b-a)) = 0$ \
$integral_a^b f(x) = integral_(1/(b-a))^(+oo) f(b-1/t)dot 1/t^2 d t$

==
Рассмотрим случай, когда $f >= 0$. \
Тогда $F(y):= integral_a^y f(x) d x$ - возрастающая функция \
Если $y < z$, то $F(z) = integral_a^z f = integral_a^y + integral_y^z f = F(y) + underbrace(integral_y^z f, >= 0) >= F(y)$ \
то есть мы поняли, что если $f in C[a,b)$ и $f>= 0$, то $integral_a^b f$ всегда существет (но возможно $+oo$) \
== Теорема
$f in C[a,b)$ и $f >= 0$, $F(y):= integral_a^y f$ \
Тогда $integral_a^b f$ - сходится $<=>$ $F$ ограничена (сверху) \
=== Доказательство
$=>$ $integral_a^b f$ - сходится $=> exists$ конечный $lim_(y-> b-) integral_a^y f = lim_(y->b-) F(y)$ \
но $lim_(y->b-) F(y) = sup_(y in[a,b)) F(y) => F$ ограничена сверху \
$arrow.double.l$ $F$ ограничена и возрастает $=> exists$ конечный $lim_(y -> b-) F(y)$, но это и есть $integral_a^b f$ \
== Следствие (признак сравнения)
$0 <= f <= g, f,h in C[a,b)$ \
Тогда 
+ если $integral_a^b g$ сходится, то $integral_a^b f$ тоже сходится, 
+ если $integral_a^b f$ расходится, то $integral_a^b g$ тоже расходится \
=== Доказательство
1) Пусть $F(y) := integral_a^y f, G(y):= integral_a^y g => F <= G$ во всех точках \
$integral_a^b g$ - сходится $<=> G$ - ограничена сверху $=> F$ - ограничена сверху $<=> integral_a^b f$ - сходится \
2) от противного $integral_a^b g$ - сходится $=> integral_a^b f$ сходится от противного
=== Замечание 1
Достаточно выполнения неравенства $0 <= f <= g$ лишь в некоторой окрестности точки $b$  \
=== Замечание 2
неравенство $f <= g$ можно заменить на $f = O(g)$, то есть $f <= C dot g$
=== Замечание 3
Если $f >= 0$ и $f = O(1/x^(1+epsilon))$ при некотором $epsilon > 0$, то $integral_a^(+oo) f$ - сходится
== Следствие 
$f, g in C[a,b), f ,g >= 0$ Если $f tilde_(x->b-) g$, то  $integral_a^b f$ и $integral_a^b g$ ведут себя одинаково (то есть либо оба сходятся, либо оба расходятся) \
=== Доказательство
$f equiv g$ $=> f = phi dot g, lim_(x-> b-) phi(x) = 1 => 1/2 < phi(x) < 2$ в некоторой окрестности точки $b => $ в этой окрестности $f <= 2g$ и $g <= 2 f$ и признак сравнения
=== Замечание
$f >= 0$ и $integral_1^(+oo) f$ - сходится $arrow.double.not lim_(x-> + oo) f(x) = 0$
== Определение
$f in C[a,b)$ интеграл $integral_a^b j$ абсолютно сходится, если $integral_a^b abs(f)$ сходится 
== Теорема
$f in C[a,b)$. Если $integral_a^b f$ абсолютно сходится, то он сходится 
=== Доказательство
$f_+ = max{f, 0}, f_- max{-f ,0}, f = f_+ - f_-, abs(f) = f_+ + f_-$ \
В частности $0 <= f_plus.minus <= abs(f)$ \
из признака сравнение $integral_a^b f_plus.minus$ - сходится $=> integral_a^b f = integral_a^b (f_+ - f_-)$ сходится 
== Признак Дирихле
$f, g in C[a, +oo)$ \
Тогда если:
+ $integral_a^b f =: F(y)$ - ограниченная функция
+ $g$ - монотонная функция
+ $lim_(x->+oo) g(x) = 0$
Если эти три условия выполнены, то тогда интеграл $integral_a^(+oo) f g$ - сходящийся 
=== Доказательство
Доказательство для случая $g in C^1[1; +oo)$ \
$integral_a^y f g = integral_a^y F`g = F g |_a^y - integral_a^y F g`$ \
Надо доказать, что $integral_a^y f g$ имеет конечный предел при $y->+oo$ \
$F g |_a^y = F(y) g(y) - underbrace(F(a) g(a), = 0) ->_(y->+oo) 0$ $F$ - ограниченная $g$ - бесконечно малая $=> F g$  бесконечно малая \
Осталось понять, что существует конечный $lim_(y->+oo) integral_a^y F g`$, то есть xnj $integral_a^(+oo) F g`$ сходится \
проверм, абсолютную сходимость $integral_a^(+oo) abs(F g`)$, $F$ - ограниченная функция $=> abs(F) <= M$ \
$integral_a^y abs(F g`) <= M integral_a^y abs(g`)$, $g$ монотонная $=> g`$ знакопостоянна, тогда получается, что $M integral_a^y abs(g`) = M abs(integral_a^y g`) = M abs(g(y) - g(a)) ->_(y->+oo) M abs(g(a))$ \ 
$=> integral_a^(+oo) M abs(g`)$ - сходится $=> integral_a^(+oo) abs(F g`)$ - сходится $=> integral_a^(+oo) F g`$ - сходится
== Признак Абеля
$f,g in C[a,+oo)$  \
Тогда если 
+ $integral_a^(+oo) f$ сходится, 
+ $g$ монотонная, 
+ $g$ ограничена
то $integral_a^(+oo) f g$ - сходится 
=== Доказательство
$g$ монотона и ограничена, значит есть конечный предел $lim_(y->+oo) g(y) =: l in RR$ \
$overline(g(y)) := g(y) - l$ - монотонна и $->_(y->+oo) 0$ \
$F(y) := integral_a^y f$ имеет конечный предел при $y->+oo$ \
$=>$ при $y > y_*$ $F(y)$ близко к этому $lim$ и, в частности, ограничена на $[a, y_*]$ $F$ ограничена, так как это непрервыная функция, значит $F$ - ограничена \
то есть функии $f$ и $overline(g)$ подходят под условия принципа Дирихле $=> integral_a^(+oo) f overline(g)$ - сходится \
$integral_a^(+oo) f g = integral_a^(+oo) f (overline(g) + l) = l integral_a^(+oo) f + integral_a^(+oo) f overline(g)$ - первое сходится по условия, второе доказали, что сходится \
== Замечание
пусть $f$ непрерывна с периодом $T$ \
Тогда $integral_a^(a+T) f = integral_b^(b+T) f$ \
=== Доказательство
$integral_b^(b+T) f(t) d t = integral_b^(b+T, =s) f(underbrace(t + T, =s)) d t = integral_(b+T)^(b+2T) f(s) d s$ \ \
$integral_a^(a+T) f = integral_a^b f + integral_b^(a+t) f = integral_(a+T)^(b+T) f + integral_b^(a+T) f = integral_b^(b+T) f$ \
$integral_a^b f = integral_a^b f(t + T) d t = integral_(a+T)^(b+T) f(s) d s$
== Замечание
$f$ непрерывна и периодична $=> f$  ограничена \
$T$ - периодична $=>$ все свои значения $f$ принимает на отрезке $[0, T]$, а там она ограничена по т. Вейерштрасса
== Следствие пр. Дирихле
$f in C[a,+oo)$, периодична с периодом $T$, $g in C[a,+oo)$ монотонна и $lim_(x->+oo) g(x) = 0$. Тогда \
+ если $integral_a^(+oo) abs(g)$ сходится,то $integral_a^(+oo) abs(f g)$ сходится \
+ Если $integral_a^(+oo) g$ - расходится, то $integral_a^(+oo)f g$ - сходится $<=> integral_a^(a+T) f = 0$ \
=== Доказательство
1) $f$ непрерывна и периодична $=> $ ограничена $=> abs(f) <= M => abs(f g) <= M abs(g)$ и пр. сравнения \
2) $arrow.double.l$ $integral_a^(a+T) f = 0 => F(y) := integral_a^y f$ - периодична \
$F(y+T) = integral_a^(y+T) f = integral_a^y f + underbrace(integral_y^(y+T) f, =0) = integral_a^y f = F(y) => F$ -периодична и непрерывна $=> F$  ограничена \
все условия принципа Дирихле выполнены $=> integral_a^(+oo) f g$ сходятся \
$=>$ \
От противного пусть $K:= integral_a^(a+T) f != 0$ \
$overline(f)(x) := f(x) - K/T$ - периодична \
$integral_a^(a+T) overline(f) = 0 => integral_a^(+oo) overline(f) g$ - сходится \ 
$integral_a^(+oo) f g = underbrace(integral_a^(+oo) overline(f) g, "сходится") + K/T underbrace(integral_a^(+oo) g, "расходится")$ \
=== Пример
$integral_1^(+oo) (sin x)/x^p d x$ \
1. $p > 1$ $abs((sin x)/x^p) <= 1/x^p$ и $integral_1^(+oo) (d x)/(x^p)$ - сходится $=> (*)$ сходится 
2. $0 < p <= 1$ $integral_0^(2 pi) sin x d x = 0, 1/x^p$ монотонно убывает и стремится к $0$, тогда второе следствие говорит, что интеграл сходящийся \
  $integral_0^(2pi) abs(sin x) d x = 4 1/x^p$ монотонно убывает и стремится к 0 и $integral_1^(+oo) (d x)/(x^p)$ - расходится 
3. $p<=0$ нет сходимости \ $integral_(pi/6 + 2 pi k)^((5pi)/6 + 2 pi k) (sin x)/x^p  d x >= 1/2 integral_(pi/6 + 2pi k)^((5pi)/6 + 2pi k) (d x)/(x^p) >= 1/2 ((5pi)/6 - pi/6) = pi/3$ - противоречит критерию Коши


=  Анализ в метрических пространствах

= Метрические нормированные пространстве
== Определение
$X$ - множество $rho: X times X -> RR$ \
$rho$ называется метрикой (расстоянием) если выполняются три свойства:
+ $rho(x, y) >= 0 and rho(x,y) = 0 <=> x=y$
+ $rho(x,y) = rho(y,x), forall x,y$
+ Неравенство треугольника $rho(x,z) <= rho(x,y) + rho(y, z) forall x,y,z in X$

== Определение
Метрическое пространство $(X, rho), X$ - множество, $rho$ - метрика \
== Примеры
+ $X= RR, rho(x,y) = abs(x-y)$
+ $X= RR^2, rho(x,y)$ - обычное расстояние
+ Дисерктная метрика (метрика лентяя) $X$ - произвольная $rho(x,y) = (x==y) ? 0: 1$
+ $RR^d = {(x_1, x_2, dots x_d) : x_1, x_2, dots x_d in RR}, rho(x,y) := (abs(x_1-y_1)^p + dots + (x_d-y_d)^p)^(1/p), p >= 1$ \ неравество $Delta$ - неравенство Минковского \ Частные случаи $d = 2, p = 2$ - стандартное расстояние на плоскости \ $d=2, p = 1, rho(x,y) = abs(x_1-y_1) + abs(x_2-y_2)$ - Манхеттенская метрика
+ $X = C[a,b]$ - равномерная метрика $rho(f,g):= max_(x in [a,b]) abs(f(x) - g(x))$
+ $X = C[a,b], rho(f,g) := integral_a^b abs(f(x) -g(x)) d x$
+ Метрика Хенминга $a:= a_1, a_2, dots a_n, b:= b_1, b_2, dots b_n$ - наборы букв, $rho(a,b) =$ количество позиций, в которых эти наборы отличаются ($a_i != b_i$)
== Определение
$(X, rho)$ - метрическое пространство, $a in X, r > 0$ \ Открытый шар с центром в точке $a$ и радиусом $r$ называется $B_r (a):= {x in X : rho(x,a) < r}$
== Определение
Замкнутый шар тоже самое, только $<=$, обозначается $overline(B)_r (a)$
== Свойства
+ $B_r_1 (a) inter B_(r_2) (a) = B_(min{r_1, r_2}) (a)$ 
+ $B_r_1 (a) union B_r_2 (a) = B_(max{r_1, r_2}) (a)$
+ Если $a != b$, то найдется такой $r>0$ для которого $overline(B_r) (a) inter overline(B_r) (b) = emptyset$ \ Доказательство: $r:= 1/3 rho(1/3)$. От противного, пусть пересекаются. Пусть $x in B_r (a) union B_r (b)$, тогда $rho(a,b) <= rho(a,x) + rho(x,b) <= r + r = 2/3 rho(a,b)$. Противоречие
== Определение
$(X, rho)$ - метрическое пространство, $A subset X$, множество $A$ назовем открытым, если $forall a in A$ $exists r > 0$, такой что $B_r (a) subset A$
== Теорема (свойства открытыъ множеств)
+ пустое и все $X$ - открытые множества
+ Объединение любого количества открытх множеств - открытое множество
+ аналогично с пересечением
+ Открытый шар это открытое множество 
=== Доказательство
1. Очев
2. Пусть $U_alpha$ - открытые множества $alpha in I$. $U:= union.big_(alpha in I) U_alpha$ надо доказать, что $U$ - открытое. Возьмем $a in U$. Тогда $a in U_alpha_0$ для некоторого $alpha_0$. $U_alpha_0$ - открытое $=>$ найдется $r>0$ для которого $B_r (a) subset U_alpha_0$. $B_r (a) subset U_alpha_0 subset U$
3. $U_1, U_2, dots, U_n$ - открытые множества $U:= inter.big_(k=1)^n U_k$. Возьмем $a in U => a in U_k forall k$. $U_k$ - открытое $=>$ найдется $r_k > 0$, для которого $B_r_k (a) subset U_k$ \ $r := min{r_1, r_2 dots r_n} => B_r (a) subset B_r_k (a) subset U_k => B_r (a) subset U$
4. $B_R (a)$ - открытое множество. Возьмем $b in B_R (a)$ \ $rho(a,b) < R$ положим $r:= R - rho(a,b)$ и проверим, что шарик $B_r (b) subset B_R (a)$ возьмем $x in B_r (b) => rho(x, b) < r$ \ Тогда $rho(x,a) <= rho(x, b) + rho(b,a) < r + rho(b, a) = R$
=== Замечание
Пересечения бесконечного числа открытых множеств не обязательно открытое. Контрпример $X = RR, rho(x,y) = abs(x-y)$. $U_n = (-1-1/n, 1+1/n), inter.big_(k=1)^oo U_n = [-1,1]$ - не открытое множество 
== Определение
$(X, rho)$ - метрическое пространство $A subset X, a in A$ \
$a$ - внутренняя точка множества $A$, если найдется $r > 0$, такое что $B_r (a) subset A$
=== Замечение
Множество открытое = все его точки ввнутренние
== Определение
Внутренность множества - это все его внутренние точки. Обозначается $"Int" A$ (альтеранитовное $A^circle.small$)\ 
=== Пример
$"Int" [-1,1] = (-1,1)$
=== Свойства внутренности множества
+ $"Int" A subset A$
+ $"Int" A$ - объединение всех открытых множеств, содержащихся в $A$. \ Доказательтво $U_alpha$ - всевозможные множества $subset A$ \ $U:= union.big_(alpha in I) U_alpha$ надо доказать, что $U = "Int" A$ \ "$subset$" Возьмем $a in U => a in U_alpha_0$ для некоторого $alpha_0$, $U_alpha_0$ - открытое, тогда найдется $B_r (a) subset U_alpha_0 subset A => a$ - внутрення точка, то есть $a in "Int" A$ \ "$supset$" Возьмем $a in "Int" A => a$ внутренняя точка $=>$ найдется $r>0$, такой что $B_r (a) subset A$, но $B_r (a)$ - открытое множество $=>$ $B_r (a)$ есть среди тех множество, которые мы объединяем $=> a in B_r(a) subset U$
+ $"Int" A$ - открытое множество. \ Доказательство: из 2 $"Int" A$ - объединение открытых множеств, что по теореме открытое множество
+ $A$ - открытое $<=> "Int A" = A$ \ $< =$ из 3. \ $=>$ Если $A$ открыто, тогда по пункту 2 среди объединений будет и $A => "Int" A subset A$
+ $A in B => "Int" A subset "Int" B$ \ Доказательство \ внутренняя точка множества $A$ является внутренней точкой множества $B$
+ $"Int" ( "Int" A) = "Int" A$ \ Доказателсьвто $3+4 => 6$
=== Упражнение
+ Доказать, что $"Int" (A inter B) = "Int" A inter "Int" B$
+ Доказать, что $"Int" (A union B) != "Int" A union "Int" B$

== Определение
$A$ - замкнутое множество, если $x \ A$ - открытое
== Теореме (свойства замкнутых множеств)
+ $emptyset, X$ - замкнутое
+ Пересечение любого количества замкнутых - замкнуто
+ Объединение конечного количество замкнутых - замкнуто
+ Замкнутый шар - замкнутое множество
=== Доказательство
+ очев
+ Есть $A_alpha$ - замкнутые. $inter_(alpha in I) A_alpha =: A$ \ $X \\ A = X \\ inter_(alpha in I) A_alpha = union_(alpha in I) X \\ A_alpha$ - открытое $=>$ $A$ - замкнуто
+ $A_1, A_2, dots, A_n A:= inter.big_(k = 1)^n = A_k$ \ $X \\ A = X \\ union.big_(k=1)^n A_k = inter.big_(k=1)^n X\\ A_k$ - открытое $=> A$ - замкнутое
+ $overline(B)_R (a)$ - замкнутое множество, то есть $underbrace(X \\ overline(B)_R (a), ={x in X : rho(a, x) > R})$ - открытое \ Возьмем $b$, такой что $rho(a,b) > R$, надо доказать, что найдется $r>0$, такой что $B_r (b) subset X \\ overline(B)_R (a)$ \ $r := rho(a,b) - R > 0$, проверим, что подходит \ Хотим доказать, что $B_r (b) inter overline(B)_R = emptyset$. От противного, возьмем $x in B_r (b) inter overline(B_r) (a)$ \ $rho(x, b) < r and rho(a, x) <= R$ \ $=> rho(a,b) <= rho(a,x) + rho(x,b) < R + r = R + (rho(a,b) - R) = rho(a,b)$ противоречие
=== Замечание
Объединение бесконечного количества замкнутых множеств может не быть замкнутым \ 
Пример: $X = RR, rho(x,y) = abs(x-y)$ \ 
$union.big_(n=1)^oo [-1+1/n; 1-1/n] = (-1,1)$ не является замкнутым 
== Определение
Замыкание множества $A$ \ пересечение всех замкнутых множеств, содержащих $A$. Обохначает $"Cl" A$ альтеранитва ($overline(A)$) \
== Теорема
$X \\ "Cl" A = "Int"(X \\ A)$, $X \\ "Int" A = "Cl" (X \\ A)$ 
=== Доказательство
"$subset$" $"Cl" A = inter.big_(F - "замкнутое", F supset A) F$, тогда $X \\ "Cl" A = union.big_(F - "заммнкуто", F supset G) = union.big_(G - "открытое", G subset X \\ A)  G = "Int"(X \\ A)$ 
=== Свойства
+ $"Cl" A$ - замкнутое множество \ Доказательство пересечение замкнутых замкнуто
+ $"Cl" A supset A$ \ Доказательство: так как перечекаем множества, содержащие $A$
+ $A$ - замкнуто $<=> A = "Cl" A$. \ Доказательство: "$arrow.double.l$" свойство 1 \ "$=>$" $A$ - замкнуто $=> $ множеств, которые пересекаем есть $A => "Cl" A subset A =>^"св. 2" "Cl" A = A$
+ $A subset B => "Cl"A subset "Cl" B$ \ $A subset B => X \\ A supset X \\ B => "Int" (X \\ A) supset "Int" (X \\ B) => (X \\ "Int"(X\\A) subset X \\ "Int"(X\\B)$
+ $"Cl"("Cl" A) = "Cl" A$. Доказательство $1 + 3 => 5$
=== Упражнения
+ $"Cl" ( A union B) = "Cl" A union "Cl" B$ 
+ для пересечений неверно
+ $A, "Int" A, "Cl" A, "Cl" "Int" A, "Int" "Cl" A, "Int" "Cl" "Int" A dots$ какое наибольшее количество различных множество может получиться?
== Теорема
$a in "Cl" A <=> forall r > 0, B_r (a) inter A != emptyset$
=== Доказательство
$"Cl" A = X \ "Int" (X \\ A), a in "Cl" A <=> a in.not "Int" (X \\ A) <=>$ какой бы ни взять $r>0$ $B_r (a) subset.not X \\ A$, то есть $B_r (a) inter A != emptyset$
== Определение
$(X, rho)$ - метрические пространство. $a in X$, окрестность точки $a$ назовем шарик $B_r (a)$ для некоторого $r>0$
== Определение
Проколотая окрестность $circle(U)_a := U_a \\ {a} = B_r (a) \\ {a}$
== Определение
$a$ - предельная точка множества $A$ \ Если в любой проколотой окрестности точки $a$ есть точки множества $A$. Обозначение $A`$ множества всех предельных точек $A$
== Теорема
$A$ - множество. Следующие условия равносильны
+ $a in A`$
+ $forall r > 0$ в шарике $B_r (a)$ содержится бесконечное количество точек множества $A$
+ Существует такая последовательность различных точек $x_n in A,$ что $rho(r_n, a) -> 0$
+ Существует такая последовательночть точек $x_n in A$, что $rho(x_n, a) -> 0$ и строго убывает
== Доказательство
"$4 => 3$" очевидно \
"$3=>2$" возьмем $r>0 => $ при больших $n: rho(x_n, a) < r => x_n in B_r (a)$ при больших $n$ \
"$2=>1$" В $B_r (a) inter A$ - бесконечное количество точек. \ В $circle(B_r)(a) inter A = (B_r (a) inter A) \ {a}$ - бесконечное количество точек $=> circle(B_r) (a) inter A != emptyset => a-  $ предельная точка множества $A$
"$1=>4$" Возьмем $r_1=1$, тогда $circle(B_r) (a) inter A != emptyset =>$ найдется $x_1 in A$ и $0 < rho(a, x_1) < 1$ \ Возьмем $r_2 := rho(a, x_1)/2 < 1/2, circle(B_r) (a) A != emptyset => $ найдется $x_2 in A$ и $0 < rho(a,x_2) < rho(a,x_1)$ \ Возьмем $r_3 := rho(a,x_2)/2 < 1/4$... \
и так далее \ В итоге получается, что $rho(a, x_k) < 1/2^k => lim rho(a,x_k) -> 0$
== Свойства предельных точек
+ $"Cl" A = A union A`$
+ $A subset B => A` subset B`$
+ $A$ - замкнуто $<=> A` subset A$
=== Доказательство
1. $A in "Cl" A <=> forall r > 0, B_r (a) inter A != emptyset$ Возьможны два варианта: 
  + $a in A$
  + $a in.not A$ и $circle(B)_r (a) inter A != emptyset$
2. Очевидно
3. $A$ - замкнуто $<=> A = "Cl" A <=> A = A union A` <=> A` subset A$