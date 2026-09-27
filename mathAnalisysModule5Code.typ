#import "@preview/theorion:0.6.0": *
#import cosmos.rainbow: *
#show: show-theorion


#show math.equation: set text(size: 1.1em)

== Экстремумы

#definition[
  $f: D -> RR, D subset RR^n, D$ - открытое, $a$ - точка нестрогого локального максимума, если $exists$ окрестность $U_a$, такая что $f(a) >= f(x)" "forall x in U_a$

  Для строгого, и обоих минимумов - загадка, сам хз
]

#definition[
  $a$ - точка экстремума, если $a$ - точка локального максимума или минимума
]

#theorem[Необходимое условие экстремума][
  $f: D -> RR, D subset RR^n, a$ - точка экстремума, тогда если существует $(partial f)/(partial x_k) (a)$, то $(partial f)/(partial x_k) (a) = 0$

  А если же $f$ дифференцируема в точке $a$, то $(partial f)/(partial x_1) = dots = (partial f)/(partial x_n) = 0$, то есть $gradient f(a) = 0$
]

#proof[
  Пусть $a$ - локальный максимум, $g(t) := f(a_1, dots a_(k-1), t, a_(k+1), dots, a_n), a_k$ - локальный максимум для $g$, $g(a_k) = f(a)$

  $0 = g'(a_k) = (partial f)/(partial x_k) (a)$ (здесь мы используем необходимое условие для функции одной переменной)
]

#definition[
  $a$ - стационарная точка, если $gradient f(a) = 0$
]

== Рубрика "Воспоминания"

В этот раз гостем нашей рубрики будет формула Тейлора и Квадратичная форма. Запишем ее до второго порядка:

$f(a+h) = f(a) + 1/2 sum_(i,j = 1)^(n) (partial^2 f)/(partial x_i partial x_j) (a) h_i h_j + o(norm(h)^2)$

Теперь вытащим $sum_(i,j = 1)^(n) (partial^2 f)/(partial x_i partial x_j) (a) h_i h_j$, скажем, что $(partial^2 f)/(partial x_i partial x_j)(a)$ - просто какой-то коэффициент (обозначим его $c_(i j)$) и: $Q(h) := sum_(i, j = 1)^(n) c_(i j) h_i h_j$ - квадратичная форма

Обычно $c_(i j) = c_(j i)$ (в нашем случае так уж точно, так как мы вообще определяли ряд Тейлора только для тех функций, у которых все частные производные, вплоть до нужного нам порядка, непрерывно дифференцируемы)

#definition[Положительная определенность из воспоминаний][
  $Q$ строго положительная определенная, если $forall h in RR^n, h !=0: Q(h) > 0$

  (нестрогую и обе отрицательные определенности довоспоминайте сами)
]

Конец воспоминаний, возвращаемся к нашим баранам

== Бараны

#lemma[
  Если $Q(h)$ строго положительно определена, то $exists c > 0$, такой что $Q(h) >= c norm(h)^2 " " forall h in RR^n$
]

#proof[
  Рассмотрим $Q$ на единичной сфере

  $Q > 0$ на единичной сфере

  $Q$ принимает на единичной сфере наименьшее значение (сфера же компакт, все же помнят теорему Вейерштрасса из третьего модуля, так ведь? Вот-вот)

  Пусть $c$ - это наим. значение, тогда $Q(h) >= c " " forall h$ с единичной сферы

  $Q(h) = Q(h/norm(h))dot norm(h)^2 >= c norm(h)^2$
]

#theorem[Достаточное условие экстремума][
  $f: D -> RR, D subset RR^n, D$ - открытое, $a in D$ - стационарная точка, $f$ дважды непрерывно дифференцируема

  Тогда:
  1. (2.) Если $Q$ строго положительно (отрицательно) определена, то $a$ - точка строгого локального минимума (максимума)
  3. (4.) Если $a$ - точка нестрогого локального минимума (максимума), то $Q$ нестрого положительно (отрицательно) определена
]

#warning-block[Если у $Q$ нет нестрогой знакоопределенности, то $a$ yt njxrf экстремума]

#proof[

  $f(a+h) - f(a) = 1/2 Q(h) + o(norm(h)^2)$

  1.  По лемме $Q(h) >= c norm(h)^2$

  $f(a+h) - f(a) >= c/2 norm(h)^2 + o(norm(h)^2) = norm(h)^2 (c/2 + o(1)) > 0$, так как второе $>0$ при малых $h$

  3. $h in RR^n, h != 0$ - фиксированный. $0 <= f(a + t h) - f(a) = 1/2 Q(t h) + o(t^2) =$

  трюк: $norm(t h)^2 = t^2 norm(h)^2$, так как $h$ фиксированный

  В итоге получаем, что $= t^2/2 Q(h) + o(t^2)$

  $0 <= (f(a+t h) - f(a))/t^2 = Q(h)/2 + o(1) -->_(t->0) Q(h)/2 => Q(h) >= 0$
]

#definition[
  $f: D -> RR, D subset RR^(n+m), a in D$

  $Phi: D -> RR^m, Phi(a) = 0$

  $a$ - точка строгого условного максимума при условии $Phi = 0$, если $exists$ окрестность $U_a$, такая что $f(a) > f(x)$ для любого $x in dot(U)_a$ удовлетворяющего условию $Phi(x) = 0$
]

#theorem[Метод множителей Лагранжа][
  $f: D -> RR, D subset RR^(n+m), a in D$

  $Phi: D -> RR^m, Phi(a) = 0, Phi$ - непр. дифф, $f$ - дифф

  Если $a$ - точка условного экстремума (при условии $Phi = 0$), то $gradient f(a), gradient Phi_1 (a), dots, gradient Phi_m (a)$ линейно зависимы
]

#note[
  1. Если $gradient Phi_1 (a), dots, gradient Phi_m (a)$ линейно зависимы, то метод бесполезен, то есть: \ $Phi`(a) = vec(gradient Phi_1(a), dots, gradient Phi_m (a))$ - у этой матрицы $m$ строк и $n+m$ столбцов, также из-за линейной зависимости rank $Phi`(a) < m$
  2. Если $gradient Phi_1 (a), dots, gradient Phi_m (a)$ линейно независимы (rank $Phi`(a) = m$), то $gradient f(a) = lambda_1 Phi_1 (a) + dots + lambda_2 Phi_m (a)$ (это и будем доказывать)
]

#proof[
  $"rank" Phi`(a) = m,$ переставляем столбики так, что 
  #image("AISelect_20260903_193227_Samsung Notes.jpg")
  пусть $a = (b, c), b in RR^n, c in RR^m$

  Пусть $a$ - точка условного максимума

  $exists$ по теореме о неявной функции $g: W -> RR^m$ непрерывно дифференцируема и $g(b) = c$, такая что $Phi(x, g(x)) equiv 0$ при $x in W$

  $h(x) = f(x, g(x)), h: W -> RR$

  $h(b) = f(b, g(b)) = f(b,c) = f(a)$

  $h(x) <= h(b)$ для близких к $b$, то есть $b$ - нестрогий локальный максимум функции $h$ 
  $=> h`(b) = 0$

  $h(x) = f(x, g(x)), h`(x) = f`(x, g(x)) dot vec(id, g)` = f`(x, g(x)) vec(E, g`(x))$ - здесь второй множитель это матрица, а не просто вектор из двух строчек

  Далее раздебоширим $f$ по иксам и игрекам, сделаем переобозначение $f = (f_x` | f_y`)$

  $= (f_x` | f_y`) vec(E, g`(x)) =  f_x` (x, g(x)) + f_y` (x, g(x)) g`(x)$

  $0 = g`(b) = f_x`(a) + f_y`(a) dot g`(b)$

  $Phi_x`(a) + Phi_y`(a) g`(b) = 0$ (это мы имеем, так как  $Phi(x, g(x)) equiv 0$), также незабиываем, что матрица $(Phi_x` | Phi_y`)$ имеет m строк, у $Phi_x$ n столбцов, у $Phi_y$ - m

  Возьмем строку $lambda in RR^m$ и умножим слева на $lambda$

  $f_x`(a) - lambda Phi_x`(a) + f_y`(a) dot g`(b) - lambda Phi_y`(a) dot g`(b) = f_x`(a) - lambda Phi_x`(a) + (f_y`(a)- lambda Phi_y`(a)) dot g`(b)$

  так как у $Phi_y` (a)$ не нулевой определитель, то можно подобрать $lambda$ так, чтобы $f_y`(a)- lambda Phi_y`(a) = 0$

  Значит $f_x`(a) - lambda Phi_x`(a) = 0$

  В итоге $f`(a) - lambda Phi`(a) = 0$, что нам и нужно было
]

#definition[
  функция Лагранжа - $f - lambda_1 Phi_1 - dots - lambda_m Phi_m$
]

#example[Наибольшее и наименьшее значение квадратичной формы на сфере][
  $S = {x_1^2 + x_2^2 + dots + x_n^2  = 1}, Phi(x) = sum_(k=1)^n x_k^2 - 1$

  $Q(x) = sum_(i, j = 1)^(n) c_(i j) x_i x_j$

  $Phi`(x) = (2 x_1, 2 x_2, dots, 2 x_n)$

  Нужно найти, что $Q`(a) - lambda Phi`(a) = 0, lambda in RR$

  $(partial Q)/(partial x_k) (x) - lambda (partial Phi)/(partial x_k) (a) = 0$, вычитаемое мы знаем, это $2 a_k$

  $(partial Q)/(partial x_k) = sum_(i=1)^n c_(i k) x_i + sum_(j=1)^n c_(k j) x_j = 2 sum_(i=1)^n c_(i k) x_i =
  $
  
  Иллюстрация:$mat(c_(11), dots, c_(1 n); c_(2 1), dots, c_(2n); dots.v,,dots.v;c_(k 1), dots, c_(n n)) vec(x_1, x_2,dots.v,x_n)$

  $= 2 C_k x$

  $Q`(a) = 2 C a$

  $Phi`(a) = 2 a$

  $Q`(a) - lambda Phi`(a) = 2 C a - 2 lambda a = 0$

  $C a = lambda a => a$ - собственный вектор, $lambda$ - собственное число этого вектора

  $Q(a) = chevron C a, a chevron.r = chevron lambda a, a chevron.r = lambda chevron a, a chevron.r = lambda norm(a)^2 = lambda$
]

#theorem[
  Наиб (наим) значение квадратичной формы на единичной сфере - наиб (наим) собственное число ее матрицы и оно достигается на соответствеующем союственном векторе
]

#corollary[
  $A: RR^n -> RR^n$,
  $norm(A) = max {sqrt(lambda): lambda - "с.ч" A^T A}$
]

#proof[
  $norm(A)^2 = sup_(norm(x) = 1) norm(A x)^2 = max_(norm(x) = 1) chevron A x, A x chevron.r = max_(norm(x) = 1) chevron A^T A x, x chevron.r$ (здесь можно заменить sup на max, так как мы находимся на компакте)
]

== Лирическое отступление

На этом моменте ув. Александру Игоревичу поступил вопрос из зала, суть его примерно в этом: "А почему мы уверены, что у нас не вылезет бесконечное число точек, которые придется проверять на то, что они экстремумы?"

Ув. Александр Игоревич привел доказательство, что, скорее всего, все будет хорошо:

$f: D -> RR, D subset RR^(n+m), Phi: D -> RR^m$

$F = f - lambda_1 Phi_1 - dots - lambda_m Phi_m$

$(partial F)/(partial x_1) (a) = dots = (partial F)/(partial x_(n+m)) (a) = 0$ - $n+m$ уравнений

Всего у нас $n+ 2m$ неизвестных, что-то как-то маловато условий, но тут вспоминаем:

$Phi_1(a) = dots = Phi_m (a) = 0$ - $m$ уравнений, кол-во уравнений = кол-во неизвестных, поэтому чаще всего конечное количество точек

Конец лирического отступления

= Глава Теория меры

== Системы множеств

Фиксируем множество $X$ и рассмотрим его подмножества

Обозначение: $A union.sq B$ - объединение множества, но при этом $A inter B = emptyset$ (дизъюнктное объединение)

И более общо: $union.sq.big_(alpha in I) A_alpha$ - объед. множеств с условием, что $A_alpha inter A_beta = emptyset (alpha != beta)$

#definition[
  Множества $E_alpha$ - разбиение множества $E$, если $E = union.sq_(alpha in I) E_alpha$
]

== Рубрика "Воспоминания"

Первый курс, первая лекция: $X \\ union.big_(alpha in I) A_alpha = inter.big_(alpha in I) (X \\ A_alpha)$

$X \\ inter.big_(alpha in I) A_alpha = union.big_(alpha in I) (X \\ A_alpha)$

конец рубрики "Воспоминания"

==

#definition[
  $cal(A)$ - система подмножеств $X$

  $cal(A)$ - симметричная система, если из того, что $A in cal(A)$ следует, что $X \\ A in cal(A)$
]

#definition[
  свойство $sigma_0 " "(delta_0)$ означает, что если $A$ и $B in cal(A)$, то $A union B in cal(A) "  "(A inter B in cal(A))$

  свойство $sigma " " (delta)$ означает, что если $A_1, A_2, dots in cal(A)$, то $union.big_(n=1)^oo A_n in cal(A)"  "(inter.big_(n=1)^oo A_n in cal(A))$
]

#lemma[
  Если $cal(A)$ - симм. система, то $(sigma_0) <=> (delta_0)$ и $(sigma) <=> (delta)$
]

#proof[
  $(sigma) <=> (delta)$

  "$=>$" $A_n in cal(A) => X \\ A_n in cal(A) => union.big_(n=1)^oo (X \\ A_n) in cal(A)$, а из рубрики мы помним, что $union.big_(n=1)^oo (X \\ A_n) = X\\inter.big_(n=1)^oo A_n$

  остальное доказывается аналогично
]

#definition[
  $cal(A)$ --- алгебра множеств, если
  + $cal(A)$ симметрично
  + $emptyset in cal(A)$ (а тогда и $X in cal(A)$)
  + есть $sigma_0$ и $delta_0$
]

#definition[
  $cal(A)$ --- $sigma$-алгебра множеств, если
  + $cal(A)$ симметрично
  + $emptyset in cal(A)$ (а тогда и $X in cal(A)$)
  + есть $sigma$ и $delta$
]

#property[Свойства алгебры множеств][
  + $emptyset, X in cal(A)$
  + Если $A, B in cal(A)$, то $A \\ B in cal(A)$
  + Конечные объед и кон. пересечения множеств из $cal(A)$ лежат в $cal(A)$
]

#note[
  Если $cal(A)$ --- $sigma$-алгебра, то $cal(A)$ - алгебра
]

#example[
  + ограниченные подмножества $RR^2$ и их дополнения --- это алгебра, но не $sigma$-алгебра
  + $2^X$ --- $sigma$-алгебра
  + ${emptyset, X}$ --- $sigma$-алгебра
  + $cal(A)$ - алгебра ($sigma$-алгебра) подмножеств $X$, $Y subset X, {A inter Y: A in cal(A)}$ --- алгебра подмножеств $Y$ ($sigma$-алгебра)
  + $cal(A)_k$ --- $sigma$-алгебра подмножеств $X$. Тогда $inter.big_(alpha in I) cal(A)_alpha$ - $sigma$-алгебра подмножеств $X$
  + $A$ и $B$ - множества, тогда для полного счастья нам нужно: $emptyset, X, A, B, X \\ A, X \\ B, A inter B, A union B, X \\( A inter B), X \\ (A union B), A \\ B, B \\ A, A triangle B, X \\(A triangle B), X \\ (A \\ B), X \\ (B \\ A)$
]

#theorem[
  $cal(E)$ - семейство подмножеств $X$. Тогда существует наименьшее по включению $sigma$-алгебра $cal(A)$ подмножеств $X$, которая содержит $cal(E)$
]

#proof[
  Пусть $cal(A)_alpha$ - всевозможные $sigma$-алгебры подмножеств $X$, содержащие $cal(E)$ (такое точно есть, так как $2^X$ - такая $sigma$-алгебра)

  $inter_(alpha in I) cal(A)_alpha$ - то, что нужно
]

#definition[
  $cal(E)$ - семейство подмножеств $X$.

  Борелевская оболочка $cal(E)$ - наим. $sigma$-алгебра, содержащая $cal(E)$, обознаячается $cal(B) (cal(A))$
]

#definition[
  Борелевская $sigma$-алгебра $cal(B)^n$ - борелевская оболочка всех открытых множеств в $RR^n$
]

#definition[$R$ - кольцо множеств, если из того, что $A, B in R$ следует, что $A union B, A inter B, A \\ B in R$]

#note[
  Если добавить условие $X in R,$ то $R$ будет алгеброй
]

#definition[
  $P$ - полукольцо, если:
  - $emptyset in P$
  - $forall A, B in P => A inter B in P$
  - $forall A, B in P => exists Q_1, Q_2, dots, Q_m in P$, такие что $A \\ B = union.sq.big_(k=1)^m Q_k$
]

#example[
  #image("AISelect_20260913_090729_Samsung Notes.jpg")
]

#lemma[
  $ union.big_n A_n = union.sq.big_n (A_n \\ union.big_(k=1)^(n-1) A_k)$
]

#proof[
  Обозначим $B_n := A_n \\ union.big_(k=1)^(n-1) A_k$

  Дизъюктность $B_n$:

  $B_m subset A_m$ и если $m < n$, то $B_n subset A_n \\ A_m subset A_n \\ B_m => B_n inter B_m = emptyset$

  "$supset$" очевидно $A_n supset B_n$

  "$subset$" Возьмем $x in union.big_n A_n$, тогда $x in A_n$ для какого-то $n$. Пусть $k$ - наименьший индекс, для которого $x in A_k => x in B_k => x in union.sq B_k$
]

#theorem[
  $P$-полукольцо. Тогда:
  - Если $P, P_1, dots, P_n in P$, то $P \\ union.big_(k=1)^n P_k = union.sq.big_(j=1)^m Q_j$ для некоторых $Q_j in P$
  - Если $P_1, P_2, dots, P_n in P$, то $union.big_(k=1)^n P_k = union.big.sq_(k=1)^n union.big.sq_(j=1)^(m_k) Q_(k j)$, где $Q_(k j) in P$ и $Q_(k j) subset P_k$ (нарезаем $P$ на $Q$)
]

#proof[
  1. Докозательство индукцией по $n$. \ База - определение полукольца \ Переход $n -> n+ 1$ \ $P \\ union.big_(k=1)^(n+1) P_k = (P \\ union.big_(k=1)^n P_k) \\ P_(n+1) = union.big.sq_(j=1)^n Q_j \\ P_(n+1) = union.big.sq_(j=1)^m union.big.sq_(i=1)^m_j Q_(j i)$ (можно перенумеровать и все получится) P.S один переход мы делаем по индукции, второй мы делаем по определению

  2. $union.big_(k=1)^n P_k = union.big.sq_(k=1)^n (P_k \\ union.big_(j=1)^(k-1) P_j) = union.big.sq_(k=1)^n union.big.sq_(j=1)^m_k Q_(k j)$ в частности $Q_(k j) subset P_k$ здесь используем пункт 1
]

#definition[
  $cal(A)$ семейство подмножеств $X$, $cal(B)$ - семейство подмножеств $Y$

  Декартово произведение $cal(A) times cal(B) := {A times B: A in cal(A), B in cal(B)}$ - семейство подмножеств $X times Y$
]

#theorem[
  Декартово произведение полуколец - полукольцо
]

#proof[
  $cal(P)$ и $cal(Q)$ - полукольца, $P, P' in cal(P), Q, Q' in cal(Q)$

  $(P times Q) inter (P' times Q') = (P inter P') times (Q inter Q')$

  $(P times Q) \\ (P' times Q') = ((P \\ P') times Q) union.sq ((P inter P') times (Q \\ Q')) = (inter.big.sq_(j=1)^n P_j times Q) inter.sq ((P inter P') times union.big.sq_(i=1)^m Q_i)$
]

#definition[
  В $RR^m$ замкнутый параллелепипед. $a, b in RR^m$ $[a,b] := [a_1, b_1] times [a_2, b_2] times dots times [a_m, b_m]$

  Открытый параллелепипед очев

  Ячейка --- $(a, b] := (a_1, b_1] times (a_2, b_2] times dots times (a_m, b_m]$
]

#theorem[
  Непустая ячейка представляется в виде возрастающей последовательности замкнутых параллелепипедов, а также в виде убывающей последовательности открытх параллелепипедов
]

#proof[
  $(a, b]$ - ячейка

  $U_n := (a_1, b_1 + 1/n) times dots times (a_m, b_m + 1/n)$

  $U_1 supset U_2 supset dots supset (a, b]$

  $inter.big_(n=1)^oo U_n = (a,b]$

  $B_n := [a_1 + 1/n, b_1] times dots times [a_m + 1/n, b_m]$

  $B_1 subset B_2 subset dots subset (a,b]$

  $union.big_(n=1)^oo B_n = (a,b]$
  #image("AISelect_20260913_120525_Samsung Notes.jpg",  width: 5cm)
]

Обозначение $cal(P)^m$ - семейство ячеек из $RR^m$

$cal(P)_QQ^m$ - семейство ячеек из $RR^m$, все координаты всех вершин у которых рациональны

#theorem[
  $cal(P)^m$ и $cal(P)_QQ^m$ - полукольца
]

#proof[
  $cal(P)'$ и $cal(P)'_QQ$ - полукольца и индукционный переход с помощью теоремы о декартовом произведении полуколец $cal(P)^(m+1) = cal(P)^m times cal(P)'$
]

#theorem[
  Любое непустое открытое множество в $RR^m$ представляется в виде счетного дизъюнктного объединения ячеек

  Более того ячейки можно выбрать так, что их вершины двоично-рациональны (представляются в виде$m/2^n$)
]

#proof[
  $G$ - открытое

  $x in G =>$ найдется $B$ - открытый шар с центорм в $x$, тако что $x in B subset G$
  #image("AISelect_20260913_134416_Samsung Notes.jpg", width: 5cm)

  $=>$ найдется ячейка $A_x$, такая, чт координаты вершин двоично-рациональны и $x in A_x subset B_x subset G$

  $union.big_(x in G) A_x = G$

  Различных множеств $A_x$ не более чем счетно, выкенем повторы и останется не более чем счетное объединение

  $union.big_"нбсч" A_x = G$

  $union.big.sq_j Q_j$ - теорема о свойствах полукольца

  *Конструктивное доказательство:*

  #image("AISelect_20260913_134924_Samsung Notes.jpg",    width: 3.7cm)
]

#corollary[
  $cal(B) (cal(P)_QQ^m) = cal(B) (cal(P)^m) = cal(B)^m$
]

#proof[
  1. ($cal(B) (cal(P)_QQ^m) subset cal(B) (cal(P)^m)$) \ $cal(P)_QQ^m subset cal(P)^m subset cal(B) (cal(P)^m)$ --- $sigma$-алгебра, отсюда по минимальности $cal(B) (cal(P)_QQ^m) subset cal(B) (cal(P)^m)$
  2. ($cal(B) (cal(P)^m) subset cal(B)^m$) \ $cal(P)^m subset cal(B)^m$ \ ячейка - счетное пересечение открытых пар $=>$ ячейка $in cal(B)^m$

  3. ($cal(B)^m subset cal(B) (cal(P)_QQ^m)$) \ Рассмотрим открытое множество $G$ \ $G in cal(B)^m (cal(P)_QQ^m)$ --- $sigma$-алгебра \ $=> cal(B)^m subset cal(B)^m (cal(P)_QQ^m)$
]

== Объем и меры

#definition[
  $cal(P)$ - полукольцо, $mu: cal(P) -> [0; +oo]$

  $mu$ --- объем, если
  + $mu emptyset = 0$
  2. Если $P, P_1, dots, P_n in cal(P), P = union.big.sq_(k=1)^n P_k, mu P = sum_(k=1)^n mu P_k$ - конечная аддитивность

  $mu$ --- мера, если
  + $mu emptyset = 0$
  + Если $P, P_1, P_2, dots in cal(P), P = union.big.sq_(k=1)^oo P_k$, то $mu P = sum_(k=1)^oo mu P_k$ - счетная аддитивность
]

#note[
  $mu$ --- мера $=> mu$ --- объем
]

#exercise[
  Если $mu equiv.not +oo$ и конечно (счетно), то $mu emptyset = 0$ 
]

#example[объемы][
  + $cal(P)^1, mu (a,b] := b - a$ --- длина ячейки
  + $g: RR -> RR$ нестрого возрастает, $cal(P)^1, nu_g (a,b] := g(b) - g(a)$
  + $cal(P^m)" "lambda_m (a,b] = (b_1 - a_1) (b_2 - a_a) dots (b_m - a_m)$ --- классический объем
  + $x_0 in x, a > 0, 2^X$ \ $mu A := cases(0" если " x_0 in.not A, a" если " x_0 in A)$
  + Алгебра подмножеств $RR^2$, состоящая из всех ограниченных множеств и их дополнений \ $mu A = cases(0" если" A "- ограниченное множество",1" если" A "- неограниченное множество")$ --- объем, о не мера
]

#theorem[Свойства объема][
  $mu: cal(P) -> [0; +oo]$ объем на полукольце

  + Если $P', P in cal(P)$, такие что $P' subset P$, то $mu P' <= mu P$
  + (усиленная монотонность) Если $P, P_1, P_2, dots, P_n in cal(P)$, $P supset union.big.sq_(k=1)^n P_k$, то $mu P >= sum_(k=1)^n mu P_k$
  2'. Если $P, P_1, P_2, dots in cal(P)$, $P supset union.big.sq_(k=1)^oo P_k$, то $mu P >= sum_(k=1)^oo mu P_k$
  3. (полуаддитивность) Если $P, P_1, dots, P_n in cal(P)$ и $P subset union.big_(k=1)^n P_k$, то $mu P <= sum_(k=1)^n mu P_k$
]

#proof[
  Из 2 следует 1, так что доказываем сразу второе:

  $P \\ union.big.sq_(k=1)^n P_k = union.big.sq_(j=1)^m Q_j$ для некоторых $Q_j in cal(P)$

  $=> P = union.big.sq_(k=1)^n P_k union.sq union.sq.big_(j=1)^m Q_j => mu P = sum_(k=1)^n mu P_k + sum_(j=1)^m mu Q_j >= sum_(k=1)^n mu P_k$

  2'. $P supset union.big.sq_(k=1)^oo P_k supset union.big.sq_(k=1)^n P_k => mu P >= sum_(k=1)^n mu P_k$ и предельный переход в неравенстве

  3 . $P'_k ;= P_k inter P => P = union.big_(k=1)^n P'_k = union.big.sq_(k=1)^n union.big.sq_(j=1)^m_k Q_(k j)$, где $Q_(k j) subset P'_k subset P_k$

  $=> mu P = sum_(k=1)^n underbrace(sum_(j = 1)^m_k mu Q_(k j), <= mu P_k) <= sum_(k=1)^n mu P_k$

  $Q_(k j) subset P_k => union.big.sq_(j=1)^m_k Q_(k j) subset P_k => sum_(j=1)^m_k mu Q_(k j) <= mu P_k$
]

#note[
  1. Если $mu$ - объем на кольце $R$, $A, B in R$, $A subset B$ и $mu A < +oo$, то $mu(B\\A) = mu B - mu A$ \ $B = (B\\ A) union.sq.big A, mu B = mu(B \\ A) + mu A$

  2. $mu$ - объем на полукольце $cal(P)$ \ $R:= {union.big.sq_(j=1)^m P_j : P_j in cal(P)}$ - кольцо \ Можно доопределить $mu$ на $R$: \ $mu (union.big.sq_(j=1)^m P_j) = sum_(j=1)^m mu P_j$
]

#theorem[
  $cal(P), cal(Q)$ - полукольца подмножеств $X$ и $Y$

  $mu$ и $nu$ - объемы на $cal(P)$ и $cal(Q)$

  $lambda (P times Q) := mu P dot nu Q$, считаем, что $0 dot (+ oo) = 0$

  $lambda$ - объем
]

#proof[
  *случай 1 (простой)*
  $P = union.sq.big_(j=1)^m P_j, Q = union.big.sq_(k=1)^n Q_k$

  $P times Q = union.big.sq_(j=1)^m union.big.sq_(k=1)^n P_j times Q_k$ и надо доказать, что $lambda(P times Q) = sum_(j=1)^m sum_(i = 1)^n lambda(P_j times Q_k)$

  $mu P = sum_(j=1)^m mu P_j$ и $nu Q = sum_(k=1)^n nu Q_k$

  $lambda(P times Q) = mu P dot nu Q = sum_(j=1)^m mu P_j dot sum_(k=1)^n nu Q_k = sum_(j=1)^m sum_(k=1)^n (mu P_j dot nu Q_k) = sum_(j=1)^m sum_(k=1)^n lambda(P_j times Q_k)$

  #image("AISelect_20260913_145126_Samsung Notes.jpg", width: 3cm) - когда вот так вот красивенько все разделилось на квадратики

  *случай 2 (общий)*

  #image("AISelect_20260913_145223_Samsung Notes.jpg", width: 3cm) - а здесь вообще не красиво разделилось(

  $P times Q = union.big.sq_(k=1)^n P_k times Q_k$

  $=> P = union_(k=1)^n P_k = union.big.sq_(k=1)^n' P'_k$

  $Q = union_(j=1)^m Q_j = sum_(j=1)^m' Q'_j$

  $lambda(P times Q) = sum_k sum_j lambda(P'_k times Q'_k)$
]

#example[мер][
  + классическимй обхем - мера (потом докажем)
  + $cal(P'), g: RR-> RR$ нестрого возрастает и непрерывна справа $nu_g (a,b]:= g(b) - g(a)$ --- мера
  + $x_0 in x, a > 0,$ \ $mu A := cases(0" если " x_0 in.not A, a" если " x_0 in A)$ - мера
  + считающая мера \#$A$ - количество элементов в множестве $A$
  + $X$ - произвольное множемтво множество $T:= {t_1, t_2, dots} subset X$ \ $w_1, w_2, dots >= 0, mu A := sum_(j: t_j in A) w_j$ #image("AISelect_20260913_145933_Samsung Notes.jpg", width: 6cm)
]

#theorem[классический объем][
  $mu$ - мера
]

#proof[
  $A = union.sq.big_(n=1)^oo A_n, mu A_n = sum_(j=1)^oo w_(n j)$

  $sum_(n=1)^oo mu A_n = sum_(n=1)^oo sum_(j=1)^oo w_(n j) =^? sum w_(n g) = mu A$

  "$<=$" $sum_(n=1)^N sum_(j=1)^J w_(n j) <= sum w_(n j) => sum_(n=1)^oo sum_(j =1)^J w_(n j) <= sum w_(n j)$

  $=> sum_(j =1)^oo sum_(n=1)^oo w_(n j) <= sum w_(n j)$

  "$>=$" $S$ - частичная сумма для $sum w_(n j)$

  $=> sum_(n = 1)^N sum_(j = 1)^n w_(n j) >= S$ для некоторых $N$ и $J$,
  
  $sum_(n=1)^oo sum_(j=1)^oo w_(n j) >= sum_(n=1)^n sum_(j=1)^oo w_(n j) >= sum_(n=1)^N sum_(j = 1)^J w_(n j) >= S$
]

#theorem[
  $mu$ - объем на полукольце $cal(P)$

  Тогда $mu$ - мера $<=>$ (счетная полуаддитивность) $P, P_1, P_2, dots in cal(P)$, такие что $P subset union.big_(k=1)^oo P_k$ тогда $mu P <= sum_(k=1)^oo mu P_k$
]

#proof[
  "$<==$" $P = sum_(k=1)^oo P_k$, $mu$-объем $=> mu P >= sum_(n=1)^oo mu P_n$

  счетная полуаддитивность $=> mu P <= sum_(n=1)^oo mu P_n$

  "$==>$" $P'_k := P_k inter P in cal(P)$

  $P = sum_(k=1)^oo P'_k = sum_(k=1)^oo sum_(j=1)^m_k Q_(k j) => mu P  sum_(k =1)^oo sum_(j=1)^m_k mu P_(k j) <= sum_(k=1)^oo mu P_k$

  $Q_(k j) in cal(P)$ и $Q_(k j) subset P'_k subset P_k => union.big.sq_(j=1)^m_k Q_(k j) subset P_k$

  $=> sum_(j=1)^m_k mu Q_(k j) <= mu P_k$ (по усиленной монотонности)
]

#corollary[
  Если $mu$ --- мера, заданная на $sigma$-алгебре, то счетное объединение множеств нулевой меры -- множество нулевой меры
]

#proof[
  $A = union.big_(n=1)^oo A_n => mu A <= sum_(n=1)^oo mu A_m = 0$
]

#theorem[
  $mu$ -- объем на $sigma$- алгебре $cal(A)$. Тогда $mu$-мера $<=>$ $mu$ -- непрерывна снизу, то есть $forall A_1 subset A_2 subset A_3 dots$ из $cal(A)$ верно $mu(union.big_(n=1)^oo A_n) = lim_(n->oo) mu A_n$
]

#proof[
  "$==>$" $B_n := A_n \\ A_(n-1), A_0 = emptyset$

  $union_(n=1)^oo A_n = union.big.sq_(n=1)^oo B_n => mu(union.big_(n=1)^oo A_n) = sum_(n=1)^oo mu B_n =$
  
  $= lim sum_(k=1)^n mu B_k = lim mu (union.big.sq_(k=1)^n B_k) = lim mu A_n$

  "$<==$" $A := union.big.sq_(k=1)^oo C_k => A_n := union.big.sq C_k$

  $=> A_1 subset A_2 subset dots => mu(union.big.sq_(k=1)^oo C_k) = mu A = lim mu A_n = lim sum_(k=1)^n mu C_k = sum_(k=1)^oo mu C_k$
]

#theorem[
  $mu$ -- объем на $sigma$-аглебре $cal(A)$ и $mu X < +oo$. Тогда следующие условия равносильны:

  + $mu$ -- мера
  + $mu$ -- непрерывна сверху, то есть $A_1 supset A_2 supset A_3 supset dots$ из $cal(A)$, $mu(inter.big_(n=1)^oo A_n) = lim mu A_n$
  + $forall A_1 supset A_2 supset dots$ из $cal(A)$, т. ч. $inter.big_(n=1)^oo A_n = emptyset$ $lim mu A_n = 0$
]

#proof[
  "$2 => 3$" очев

  "$1 => 2$" $mu$ -- мера $=>$ непрерывная снизу

  $X \\ A_1 subset X \\ A_2 subset dots => mu (union.big_(n=1)^oo (X \\ A_n)) = lim mu(X \\ A_n)$

  "$3 => 1$" $A:= union.big.sq_(k=1)^oo C_k$

  $A_n := union.big.sq_(k = m+1)^oo C_k$, тогда $A_1 supset A_2 supset A_3 dots$

  и $inter.big_(n=1)^oo A_n = emptyset$

  $=> lim mu A_n = 0, A = union.big.sq_(k=1)^n C_k union.sq A_n => mu A = sum_(k=1)^n mu C_k + mu A_n$ (первое стремится к $sum_(k=1)^oo mu C_k$, второе к $0$)
]

#note[
  Условие $mu X < + oo$ важно

  Пример $RR, lambda_1$ - длина

  $inter.big_(n=1)^oo (n, +oo) = emptyset, lambda_1 (n, +oo) = +oo$
]

#corollary[
  $mu$ --- мера $A_1 supset A_2 dots, mu A_m < +oo$ для некоторого $m$

  Тогда $mu(inter_(n=1)^oo A_n) = lim mu A_n$
]

#proof[
  рассмотрим множество $A_m \\ A_k$
]

== Продолжение мер

#definition[
  $nu: 2^X -> [0, +oo]$ --- субмера, если:
  + $nu emptyset = 0$
  + монотонность. Если $A subset B$, то $nu A <= nu B$
  + счетная полуадд. Если $A subset union.big_(n=1)^oo A_n$, то $nu A <= sum_(n=1)^oo nu A_n$
]

#note[
  Из $3$ следует $2$
]

#definition[
  $mu: cal(A) -> [0; +oo]$ --- мера на $sigma$-алгебре $cal(A)$

  $mu$ - полная, если из условия, что $mu A < 0$ и $B subset A$ следует $B in cal(A)$ (и тогда $mu B = 0$)
]

#definition[
  $nu$ -- субмера. Назовем $mu$-измеримыми такие множества $E$, что $forall A subset X: nu A = nu(A inter E) + nu (A \\ E)$
]

#note[
  "$<=$" всегда верно из счетной полуаддитивности, то есть в определении можем писать "$>=$"
]

#note[
  $E_1, E_2, dots$ - дизъюнктные $nu$-измеримые множества

  Тогда $nu(A inter union.big.sq_(k=1)^n E_k) = sum_(k=1)^n nu (A inter E_k)$

  Доказательство индукцией по $n$: $nu(A inter union.big.sq_(k=1)^n E_k) = nu(A inter union.big.sq_(k=1)^(n-1 ) E_k) + nu (A inter E) = (A inter union.big.sq_(k=1)^n E_k) \\ E_n + nu (A inter union.big.sq_(k=1)^n E_k) inter E_n$
]

#theorem[Каратеодори][
  $nu$-измеримое множество образует $sigma$-алгебру (обозначим $cal(A)$).

  Сужение $nu$ на эту $sigma$-алгебру --- полная мера
]

#proof[
  + Если $nu E = 0$, то $E$ --- $nu$-измеримо (сейчас проверим) \ $nu(A inter E) + nu (A \\ E) <= nu E + nu A = nu A$

  + Проверим, что $cal(A)$-симметричная структура: \ $E$ --- $nu$-измеримо $=> nu A = nu (A inter E) + nu(A \\ E) = nu(A inter (X \\ E)) + nu (A \\ (X \\ E))$

  + Если $E$ и $F in cal(A)$, то $E union F in cal(A)$ \ $nu A = nu (A inter E) + nu (A \\ E) = nu (A inter E) + nu ((A\\E) inter F) + nu((A\\E) \ F) >= nu(A inter (E union F)) + nu(A\\(E union F)) => E union F in A$ \ Поясняющая картинка: #image("AISelect_20260927_214130_Samsung Notes.jpg", height: 4cm)

  + $cal(A)$ -- алгебра

  + $E_1, E_2, dots in cal(A)$ и дизъюнктны $=> E:= union.big.sq_(n=1)^oo E_n in cal(A)$ (хотим проверить) \ $nu A = nu (A inter union.big.sq_(k=1)^n  E_k) + nu(underbrace(A \\ union.big.sq_(k=1)^n E_k, supset A\\E)) >= nu(A inter union.big.sq_(k=1)^n E_k) + nu (A \\ E) = sum_(k=1)^n nu (A inter E_k) + nu (A \\ E)$

  + $E_1, E_2, dots in cal(A) => union.big_(n=1)^oo E_n in cal(A)$ \ Переделаем $union E_n$ в дизъюнктное объединение $union.big.sq_(n=1)^oo (E_n \\ union.big_(k=1)^(n-1) E_k) in cal(A)$

  + $cal(A)$ --- $sigma$-алгебра (полнота из первого пункта)
  + $nu_cal(A)$ --- мера. Нужно проверить, что $nu_cal(A)$ - объем (т.к. сч. полуаддитивность есть) \ Если $E_1, E_2, dots E_n in cal(A)$, то $nu (union.big.sq_(k=1)^n E_k) = sum_(k=1)^n nu E_k$ - это замечание 2 для $A = X$
]

#definition[
  $mu$ - мера на полукольце $cal(P)$

  Внешняя мера, порожденная $mu$

  $mu^* A:= inf {sum_(n=1)^oo mu P_n: P_n in cal(P) "и" A subset union.big_(n=1)^oo P_n}$

  Если такого покрытия не существует, то $mu^* A = +oo$
]

#note[
  + Можно рассмотреть лишь покрытие дизъюнктными множествами $union.big_(n=1)^oo P_n = union.big.sq_(n=1)^oo union.big.sq_(k=1)^m_n Q_(n k),$ где $Q_(n k) subset P_n$

  + Если мера $mu$ задана на $sigma$-алгебре $cal(A)$, то $mu^* A = inf {mu B: B in cal(A) "и" A subset B}$
]

#theorem[
  $mu^*$ - субмера, совпадающая с $mu$ на полукольце $cal(P)$
]

#proof[

  шаг 1.

  Возьмем $A in cal(P)$ и проверим, что $mu^* A = mu A$

  "$>=$" $A, emptyset, emptyset, dots$ - покрытие $A$ элементами полукольца $sum_(n=1)^oo mu P_n = mu A => inf <= mu A$

  "$<=$" $A subset union.big_(n=1)^oo P_n ==>_"счетная полуадд" mu A <= sum_(n=1)^oo mu P_n => mu A <= inf$

  шаг 2.

  $mu^*$ - счетно и полуаддитивно. $A subset union.big_(n=1)^oo A_n =>^? mu^* A <= sum_(n=1)^oo mu^* A_n$ (если есть $+oo$, то все очевидно)

  $mu^* A_n = inf {sum_(k=1)^oo mu P_k: A_n subset union.big_(k=1)^oo P_k "и" P_k in cal(P)}$

  Возьмем покрытие $A_n subset union.big_(k=1)^oo P_(n k)$ (можем взять благодяря $inf$), что $sum_(k=1)^oo mu P_(n k) < mu^* A_n + epsilon/2^n$

  $A subset union.big_(n=1)^oo A_n subset union.big_(n=1)^oo union.big_(k=1)^oo P_(n k)$

  $sum_(n=1)^oo sum_(k=1)^oo mu P_(n k) < sum_(n=1)^oo (mu^* A_n + epsilon/2^n) = epsilon + sum_(n=1)^oo mu^* A_n => mu^* A < epsilon + sum_(n=1)^oo mu^* A_n$ и $epsilon -> 0$
]

#definition[
  $mu$ - мера на полукольце $cal(P)$

  Стандартное продолжение меры с полукольца: строим внешнюю меру $mu^*$ и сужаем ее на семейство $mu^*$ - измеримых множеств
]

#theorem[
  Это действительно продолжение, то есть множества из $cal(P)$ являются $mu^*$-измеримыми
]

#proof[
  Надо доказать, что если $E in cal(P)$, то $mu^* A >= mu^* (A inter E) + mu(A \\ E)$

  Шаг 1. $A in cal(P)$ $A \\ E = union.big.sq_(k=1)^n Q_k$ для каких-то $Q_k in cal(P)$

  $mu^* A = mu A = mu (A inter E) + sum_(k=1)^n mu Q_k >= mu^* (A inter E) + mu^* (A \\ E)$

  Шаг 2. $A in.not cal(P)$. Если $mu^* A = +oo$, то очевидно

  Считаем, что конечно

  Возьмем покрытие $A subset union_(n=1)^oo P_n$, такое что $sum_(n=1)^oo mu P_n < mu^* A + epsilon$

  по шагу 1 $mu P_n = mu^* P_n >= mu^* (P_n inter E) + mu^* (P_n \\ E)$

  $epsilon + mu^* A > sum_(n=1)^oo mu P_n >= sum_(n=1)^oo mu^* (P_n inter E) + sum_(n=1)^oo mu^* (P_n \\ E)$

  $union.big_(n=1)^oo (P_n inter E) supset A inter E ==>_("счетная полуадд" mu^*) sum_(n=1)^oo mu^* (P_n inter E) >= mu^* (A inter E)$

  $union.big_(n=1)^oo (P_n \\ E) supset A \\ E => sum_(n=1)^oo mu^* (P_n \\ E) >= mu^* (A \\ E)$

  Значит $sum_(n=1)^oo mu^* (P_n inter E) + sum_(n=1)^oo mu^* (P_n \\ E) >= mu^* (A inter E) + mu^* (A \\ E), epsilon ->0$
]

#note[
  + Дальше стандартное проложение обозначаем той же буквой, что и исходную меру
  + Применение ст. продолжения к стандартную прололжению не дает ничего нового
  + Можно ли продолжить меру $mu$ на более широкую $sigma$-алгебру нежели $sigma$-алгебра $mu^*$ - измеримых множеств? Обычно да, но неоднозначно
]

#definition[
  $mu$ называется $sigma$-конечная мера, если $x = union_(n=1)^oo P_n$, где $mu P_n < +oo$

  + класс объем --- $sigma$-конечная мера
  + считающая мера на $RR$ - нет
]

#theorem[
  $cal(P)$ - полукольцо, $mu$-ст. продолжение с $cal(P)$

  $mu^*$ -- соответствующая внешняя мера $A subset X$, т.ч. $mu^* A < +oo$

  Тогда найдутся $B_(n k) in cal(P)$, т. ч. $C_n := union_(k=1)^oo B_(n k), C := inter.big_(n=1)^oo C_n, C supset A$ и $mu^* A = mu C$
]

#proof[
  $mu^* A = inf {sum_(k=1)^oo mu P_k : P_k in cal(P) "и" union_(k=1)^oo P_k supset A}$

  Возьмем реализацию, а которой $inf < mu^* A + 1/n$

  $B_(n k) in cal(P), C_n = sum_(k=1)^oo B_(n k) supset A$ и $ mu C_n <=sum_(k=1)^oo mu B_(n k) < mu^* A + 1/n$

  $C_n supset A$ и $mu C_n < mu^* A + 1/n$

  $C = inter_(n=1)^oo C_n supset A$ и $C subset C_n => mu^* A <= mu* C <= mu C <= mu C_n < mu^* A + 1/n$

  $=> mu^* A = mu C$
]

#corollary[
  $cal(P)$ - полукольцо, $mu$ -- ст. продолжение с $cal(P)$

  Если $mu A < +oo$ ($A - mu^*$ измер. множество), то $A = B union.sq e$, где $B in cal(B) (cal(P))$ и $mu e =0$
]

#proof[
  $C$ --- множество из теоремы $C supset A$ и $mu A = mu^* A = mu C => mu (underbrace(C \\ A,=:e_1)) = 0$, $C in cal(B)(cal(P))$

  Подставим $e_1$ в теорему, найдется $e_2 > e_1$ $mu e_2 = 0, e_2 in cal(B)(cal(P))$

  $mu (C\\ e_2) = mu C = mu A$

  #image("AISelect_20260927_223011_Samsung Notes.jpg", height: 4cm)

  Положим $B := C \\ e_2$ и $e := A \\ B$
]

#theorem[единственность продолжения][
  $cal(P)$ - полукольцо, $mu$ - ст. продолжение меры с $cal(P)$ на $sigma$-алгебре $cal(A)$, $nu$-другая мера на $A$, т.ч.  $mu E = nu E, forall E in cal(P)$. Тогда если $mu$ -- $sigma$-конечная мера, то $mu A = nu A$ $forall A in cal(A)$
]