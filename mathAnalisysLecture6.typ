Автор: FlintWithBlackCrown aka Кирилл Болохов
== Определение
Верхний предел последовательности  $overline(lim) x_n  (lim sup x_n)$ \
$overline(lim) x_n := lim sup {x_n, x_(n+1), x_(n+2), dots } = lim sup _(k>=n) x_k$, пусть $sup_(x>= n) =  z_n$\
Соглашене $lim(+infinity) = + infinity$
== Определение
Нижний предел $underline(lim) x_n (lim inf x_n)$ \
$underline(lim) x_n := lim inf {x_n, x_(n+1), x_(n+2), dots} = lim inf_(k>=n) x_k$, пусть $inf_(k>=n) x_k = y_n$\ 
Замечание $y_n <= z_n, z_n >= z_(n+1)$ и $y_n <= y_(n+1)$\
== Теорема
+ $underline(lim) x_n$ и $overline(lim) x_n$ существуюут в $overline(RR)$
+ $underline(lim) <= overline(lim)$ \
Доказательство\
+ $y_1 <= y_2 <= y_3 <= dots$ если $y_n$ ограничен сверху, то $lim y_n$ существует и конечен, если $y_n$ неограничен сверху, то $lim y_n = +infinity$, если $y_n = -infinity forall n$, то $lim y_n = -infinity$  
+ $y_n <= z_n$, $y_n -> underline(lim), z_n -> overline(lim) => underline(lim) <= overline(lim)$\
== Теорема
+ $overline(lim) x_n$ - наибольший из частичных пределов последовательности $x_n$
+ $underline(lim) x_n$ - наименьший из частичных пределов последовательности $x_n$
+ $lim x_n$ существует в $overline(RR)$  $<=> underline(lim) x_n = overline(lim) x_n$ и в этом случае они все равны
Доказательство
+ $a := overline(lim) x_n$, покажем, что $a$ это частичный предел\ случай $a in RR$, $z_1 >= z_2 >= dots$ и $z_n -> a$, $=> z_n >= a$ \ найдется такой номер, такой что $a-1 < a <=z_(m_1) < a + 1$, $z_(m_1) = sup {x_m, x_(m+1), x_(m+2), dots}$. Заметим, что $a-1$ не верхняя граница для ${x_m, x_(m+1), dots}$, тогда найдется $n_1 >= m$, такой что $x_(n_1) in (a-1, a+1)$. Найдется $m > n_1$, такое что $a + 1/2 > z_m >= a > a - 1/2$, $a-1/2$ не верхняя граница для ${x_m, x_(m+1), dots}$, значит найдется $n_2 >= m$, такой что $x_(n_2) > a - 1/2 => x_(n_2) in (a - 1/2, a + 1/2)$ \ Найдется $m > n_2$, такой что $a + 1/2 > z_m >= a >= a - 1/3$, тогда найдется $n_3 >= m$, такой что $x_(n_3) > a-1/3 => x_(n_3) in (a-1/3, a+1/3)$ и т.д.\ В итоге $n_1 < n_2 < n_3 < dots$ и $x_(n_k) in (a - 1/k, a + 1/k)$, то есть $a-1/k < x_(n_k) < a + 1/k$, тогда по теореме о двух милиционерах $=> lim x_(n_k) = a$ \ случай $a = + infinity$, тогда $x_n = + infinity forall n$, $z_1 = sup {x_1, x_2, dots} = + infinity =>$ найдется $n_1$, такой что $x_(n_1) > 1$ \ $x_(n_1 + 1) = sup {x_(n_1 + 1), x_(n_1 + 2), dots} =>$ найдтеся $n_2 > n_1$, такой что $x_(n_2) > 2$ и т.д \ $a = - infinity$ \ $lim z_n = - infinity$ и $x_n <= z_n -> -infinity => lim x_n = -infinity$ \ Покажем, что если $b$ - частичный предел, то $b <= a$ \ $b$ - частичный предел, значит найдется такая $x_(n_k)$, такая что $lim x_(n_k) = b$\ $x_(n_k) <= z_(n_k) => b <= a$
+
+ $=>$, если $a = lim x_n$, то любая подпоследовательность $x_(n_k)$ имеет предел $a$, коли так, то единственный возможный частичный предел это $a$ \ Следовательно единственный возможный частичный предел это $a$, то есть $a$ - наибольший из всех частичных пределов $=> a = overline(lim)$ и $a$  - наименьший из всех частичных пределов $=> a = lim$, следовательно $underline(lim) = overline(lim) = lim$ \ <= $y_n <= x_n <= z_n$
== Замечание
$overline(lim) x_n = lim sup_(k>=n) {x_k} = inf_n sup_(k>=n) {x_k}$, \ $underline(x_n) = lim inf_(k>=n) {x_k} = sup_n inf_(k>=n) {x_k}$ 
== Теорема 1
$a = underline(lim) x_n <=> cases(forall epsilon > 0 " " exists N " " forall n >= N => x_n > a - epsilon, forall epsilon > 0 " " forall N " " exists n >= N => x_n < a + epsilon)$
== Теорема 2
$b = overline(lim) x_n <=> cases(forall epsilon > 0 exists N " " forall n>= N => x_n < b+ epsilon, forall epsilon > 0 " " forall N " " exists n >= N => x_n > b - epsilon)$\
Доказательство \
$=>$ $z_N <= b + epsilon$ $z_N >= z_(N+1) >= z_(N+2) >= dots <=> forall n >=N " " z_n <= b + epsilon$ \
$=>$ $z_N = sup {x_N, x_(N+1), dots} > b - epsilon <=> forall N " " z_N > b - epsilon $\ из этих двух пунктов $lim z_n = b$\
$z_N <= b + epsilon => forall n >= N => x_n <= b + epsilon$ \ 1 пункт так же \
== Теорема 
Если $a_n <= b_n " " forall n$, то $underline(lim) a_n <= underline(lim) b_n$ и $overline(lim) a_n <= overline(lim) b_n$ \
Доказательство $underline(lim) a_n = lim inf{a_n , a_(n+1), dots}, underline(lim) b_n = lim {inf b_n, b_(n+1), dots}$, из этих двух пунктов получаем, что $inf{a_n, a_(n+1)} <= inf (b_n, b_(n+1))$ \
Замечание. Арифметики с $underline(lim)$ и $overline(lim)$ нет. \
= Параграф 5 Числовые ряды
== Определение 
$ sum_(k+1)^infinity a_k " - ряд" $
Частичная сумма ряда $S_n := sum_(x=1)^(n) a_k$\
Если у последовательности $S_n$ существует предел в $overline(RR)$, то он называется суммой ряда\
Ряд называется сходящимся, если $lim S_n$ существуеют и конечен \
В противном случае ряд  называется расходящимся (т.е. если $lim S_n$  не существует или $lim S_n = plus.minus infinity$)\
=== Пример 
+ Геометрическая прогрессия $ sum_(k=1)^infinity q^(k-1) = 1 + q + q^2 + dots $\ частичная сумма $S_n = 1 + q + q^2 + dots = cases((q^n-1)/(q-1) ", "q != 1, n)$ \
Если $q = 1$, то $S_n = n$, $lim X_n = + infinity$ и ряд расходится \
Если $q != 1$, то $S_n = (q^n - 1)/(q-1)$ и $lim (q^n-1)/(q-1) = cases(+infinity "при " q> 1, 1(1-q) "при " -1 < q < 1, "нет")$ \
то есть ряд сходится $<=>$ $abs(q) < 1$ и в этом случае его сумма $1/(1-q)$
=== Пример 2
$ sum_(n=1)^infinity (-1)^n $ $-1 + 1 -1 + 1 + dots$,\ $s_(2n) = 0, s_(2n + 1) = -1 =>$ нет предела\
=== Пример 3
Гармонический ряд $ sum_(k = 1)^infinity 1/n $ \
$1/(n+1) + 1/(n+2) + dots + 1/(2n) > n dot 1/(2n) = 1/2$ \ 
можем наскребсти сколь угодно большую сумму, и тогда ряд расходится
=== Пример 4
$ sum_(k+1)^infinity 1/(k (k+1))$ \
$S_n := 1/(1 dot 2) + 1/(2 dot 3) + dots + 1/(n dot (n+1)) = 1 - 1/(n+1) = n/(n+1)$, ряд сходится, его умма $= 1$
== Теорема (необходимые условия сходимости)
Если ряд $sum_(k=1)^infinity x_k$ сходится, то $lim x_n = 0$ \
Доказательство: \
$x_n = sum_(k=1)^n x_k - sum_(k=1)^(n-1) x_k = s_n - s_(n-1)$, если ряд сходится, то $lim s_n = s in RR$, $lim x_n = lim s_n - lim s = s - s = 0$
== Свойства сход. рядов
1. Единственность суммы (т.е. у ряда не может быть две разных суммы)
2. Расстановка скобок у ряда, имеющего сумму, не меняет его сумму \ 
Доказательство: \
Расстановка = выбор подпоследовательности у пследовательности частичных сумм \
Замечание у расходящегося ряда бывает можно расставить скобки так, что он станет сходящимся, например $(1-1) + (1-1) + dots = 0$ 
3. Добавление или отбрасывание конечного количества членов у сходящегося ряда не влияет на сходимость, но может менять сумму
Доказательство: \
очев
4. Если $sum_(k=1)^infinity a_k$ и $sum_(k=1)^infinity b_k$,то $sum_(k=1)^infinity (a_k + b_k)$ сходится и $sum_(k=1)^infinity (a_k + b_k)= sum_(k=1)^infinity a_k + sum_(k=1)^infinity b_k$
5. Если $sum_(k=1)^infinity a_k$ сходится, то $sum_(k=1)^infinity c a_k$ сходится и $sum_(k=1)^infinity c  a_k = c sum_(k=1)^infinity a_k$
Доказательство: \
$A_n := sum_(k=1)^n a_k$ и $B_n:= sum_(k=1)^n b_k$, ряда сходится $=> lim A_n =: A in RR and lim B_n =: B in RR => S_n = sum_(k=1)^n (a_k + b_k) = A_n + B_n -> A + B$
= Глава 3 функции одной переменной
= Параграф 1
Напоминание. окрестность точки $a in RR, U_a = (a-epsilon, a + epsilon)$ при $epsilon > 0$, $U_(+infinity) = (E, +infinity)$, $U_(-infinity) = (-infinity, E)$ \ 
== Определенеие о
крестность точки $U_a$ с точеской сверху это $U_a \ {a}$ 
== Определение
$A in RR$  $a$ - предельная точка множества $A$, если $U_a "проколотая" inter A != emptyset " " forall U_a$
== Теорема
$a in RR, A subset RR$  следующие условие расносильны
1. $a$ - предельаня точка множества A
2. В любой окрестности $U_a$ содержится бесконечное количество точек из $A$
3. Найдется такая последовательность точек $x_n in A, x_n != a$, такие что $lim x_n = a$, более того эту пследовательность всегда можно выбрать стого монотонной
Доказательство: \
$2 => 1$. Если в $U_a inter A$  бесконечное количество тоек, то в $U_a$ с точечкой сверху $inter A = (U_a inter A) \ {a}$, бесконечное количество точек $=> != emptyset$.\
$3 => 2$ Возьмем $x_n in A$, такое что $lim x_n = a$ \
Рассмотрим $U_a$ начиная с некоторого номера $cases(x_n in U_a, x_n in A) => x_n in U_a inter A => $ в $U_a inter A$ бесконечное количество точек\
$1 => 3$ множество $(a-1, a+1) inter A \\ {a} != emptyset$, возьмем оттуда точку и назовем $x_1$, эта точко точно не $a$.\
$epsilon_2 = abs(x_1 - a) / 2 > 0$ \
Множество $(a - epsilon_1, a + epsilon_2) inter A \\ {a} != emptyset$, возьмем оттуда точку, назовем $x_2$ и т.д
$abs(x_2 - a) < epsilon_1 = abs(x_1 - a)/2$ \
$abs(x_3 - a) < epsilon_3 = abs(x_3 - a)/2$
$=> abs(x_n - a) < epsilon_n = abs(x_(n+1) + a)/2 => abs(x_n - a) < abs(x_1 - a)/2^(n-1)$ \
$=>  lim abs(x_n - a) = 0$, то есть $a = lim x_n$ и все точки получились различны\
Как ее сделать строго монотонной?
с какой-то стороны от точки $a$ бесконечное количество членов последовательности, выкинем остальные, оставим только точки с одной стороны от $a$. Получилась монотонная последовательность 
== Определение
$S : E -> RR$, $a$ - предельная точка множества $A$\
$b:= lim_(x->a) f(x)$, если 
1. (по Коши) $forall epsilon > 0 " " exists delta > 0 " " forall x in E$  и $abs(x-a) < delta => abs(f(x) - b) < epsilon$
2. (определение на языке окрестностей) $forall U_b " " exists U_a$, таоке что $f (E inter U_a " с точечкой сверху") subset U_a$\
3. (опредление по Гейне) $forall$ последовательность $x_n in E$, такая что $lim x_n = a => lim f(x_n) = b$
Замечание \
1 = 2\
$U_b = (b - epsilon, b + epsilon)$ при некотором $epsilon > 0$ $forall U_b$ означает $forall epsilon > 0 " " U_b := (b- epsilon, b + epsilon)$ \
$U_a = (a - delta, a + delta)$ при некотором $delta > 0$ $exists U_a$ означает $exists delta > 0$ $U_a = (a - delta, a + delta)$ \
$f(U_a "с точечкой сверху" inter E) in U_b$ означает, что $forall x in U_a " с точечкой сверху" inter E => f(x) in U_b$, то есть $abs(f(x) - b) < epsilon$