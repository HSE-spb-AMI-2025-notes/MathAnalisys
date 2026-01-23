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