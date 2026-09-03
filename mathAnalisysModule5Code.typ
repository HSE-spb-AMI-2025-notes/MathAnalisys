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