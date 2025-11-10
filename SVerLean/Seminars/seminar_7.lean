import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Relation

open Relation

set_option linter.hashCommand false

/- # Задача 1. Расширение грамматики. -/

abbrev State := String → ℕ

inductive Stmt : Type
  | skip       : Stmt
  | assign     : String → (State → ℕ) → Stmt
  | seq        : Stmt → Stmt → Stmt
  | ifThenElse : (State → Bool) → Stmt → Stmt → Stmt
  | whileDo    : (State → Bool) → Stmt → Stmt

infixr:90 "; " => Stmt.seq

/-- Напишите функцию выполняющую программу. Мы пометили ее `partial` чтобы не
доказывать корректность рекурсии (она и некорректна).
В любом случае мы не будем ничего доказывать про эту функцию,
но она пригодится для отладки. -/
partial def Stmt.eval (state : State) (program : Stmt) : State :=
  sorry

/-- Смоделируйте цикл `for` через существующие конструкции языка WHILE. -/
def Stmt.forInRange (i : String) (start stop : ℕ) (body : Stmt) : Stmt :=
  sorry

/-- Напишите программу, которая проверяет, является ли `n` первообразным корнем по модулю `mod`.
Число `n` называется первообразным корнем по модулю `mod`, если в последовательности
`n % mod, n² % mod, n³ % mod, ..., n^mod % mod` нет повторяющихся элементов. Достаточно
проверить что среди первых `mod - 1` элементов нет равного `1`. -/
def isPrimitiveRoot (n mod : ℕ) : Stmt :=
  sorry

#guard (isPrimitiveRoot 1 3).eval (fun _ ↦ 0) "result" == 0
#guard (isPrimitiveRoot 2 3).eval (fun _ ↦ 0) "result" == 1
#guard (isPrimitiveRoot 0 5).eval (fun _ ↦ 0) "result" == 1
#guard (isPrimitiveRoot 3 7).eval (fun _ ↦ 0) "result" == 1
#guard (isPrimitiveRoot 2 7).eval (fun _ ↦ 0) "result" == 0
#guard (isPrimitiveRoot 11 7).eval (fun _ ↦ 0) "result" == 0


/- Пока что у нас отсутствуют инструкции `break` и `continue` в циклах.
Как расширить синтаксис языка таким образом чтобы добавить их и так чтобы
их нельзя было использовать вне цикла? -/

inductive Stmt'
| skip       : Stmt'
-- и так далее

partial def Stmt'.eval (state : State) (program : Stmt') : State :=
  sorry

/- Протестируйте `Stmt'.eval` на следующих программах: -/

/--
```py
while True:
  x = x + 1
  break
```
-/
def breakDemo : Stmt' := sorry

/--
```py
while True:
  i = 0
  sum = 0
  while i < 3:
    i = i + 1
    if i == 2:
      continue
    sum = sum + i
```
-/
def continueDemo : Stmt' := sorry

/--
```py
i = 0
flag = 0
while i < 1:
  i = i + 1
  if True:
    continue
  flag = 1
```
-/
def continueSkipsRestDemo : Stmt' := sorry

#guard Stmt'.eval (fun _ => 0) breakDemo "x" = 1
#guard Stmt'.eval (fun _ => 0) continueDemo "sum" = 4
#guard Stmt'.eval (fun _ => 0) continueSkipsRestDemo "flag" = 0




/- # Задача 2. Big-step семантика и неразрешимость остановки. -/

inductive BigStep : Stmt × State → State → Prop where
  | skip (s) :
    BigStep (Stmt.skip, s) s
  | assign (x a s) :
    BigStep (Stmt.assign x a, s) (Function.update s x (a s))
  | seq (S T s t u) (hS : BigStep (S, s) t) (hT : BigStep (T, t) u) :
    BigStep (S; T, s) u
  | ifTrue (B S T s t) (hcond : B s) (hbody : BigStep (S, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | ifFalse (B S T s t) (hcond : ¬ B s) (hbody : BigStep (T, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | whileTrue (B S s t u) (hcond : B s) (hbody : BigStep (S, s) t)
      (hrest : BigStep (Stmt.whileDo B S, t) u) :
    BigStep (Stmt.whileDo B S, s) u
  | whileFalse (B S s) (hcond : ¬ B s) :
    BigStep (Stmt.whileDo B S, s) s

infix:110 " ⟹ " => BigStep


/-- Докажите обратимость `if`-правила для big-step семантики. -/
theorem BigStep_if_Iff {B S T s t} :
    (Stmt.ifThenElse B S T, s) ⟹ t ↔
    (B s ∧ (S, s) ⟹ t) ∨ (¬ B s ∧ (T, s) ⟹ t) := by
  sorry

/-- Используя big-step семантику, задайте условие означающее "программа `s` завершается,
и в переменной `result` лежит наименьшее общее кратное чисел лежащих в переменных
`x` и `y` до вычисления программы `s`". -/
def GcdSpec (s : Stmt) : Prop := sorry

/-- Докажите детерминированность для big-step семантики. -/
theorem BigStep_deterministic {S s l r} (hl : (S, s) ⟹ l)
    (hr : (S, s) ⟹ r) :
    l = r := by
  sorry

/- Задача "проверить завершается ли данная программа" неразрешима.
Обычно чтобы доказать неразрешимость задачи A берут другую задачу B, про
которую известно что она неразрешима, и сводят задачу B к задаче A.

Тогда если бы задача A была разрешимой то и сведенная к ней задача B
окажется разрешимой и мы приходим к противоречию.

Давайте сведем задачу о проверке `∃ n, p n` к проблеме остановки программы.
-/

def Halts (state : State) (program : Stmt) : Prop :=
  ∃ t, (program, state) ⟹ t

-- предположим что задача о проверке остановки программы разрешима
axiom HaltDecidable (state : State) (program : Stmt) :
    Decidable (Halts state program)
attribute [instance] HaltDecidable

/-- Реализуйте этот инстанс при помощи `HaltDecidable`. -/
noncomputable instance (p : ℕ → Bool) : Decidable (∃ n, p n) :=
  let state := fun _ ↦ 0
  let program : Stmt :=
    .whileDo (fun state => !p (state "i")) (
      .assign "i" (fun state => state "i" + 1)
    )
  if h : Halts state program then
    .isTrue sorry -- не нужно доказывать. Это в принципе возможно, но сложно:
                  -- приходится вполне упорядочивать `BigStep` вручную.
  else
    .isFalse (by
      contrapose! h
      let m := Nat.find h -- наименьшее число такое что `p m = true`
      sorry
    )




/- # Задача 3. Small-step семантика и переполнение.

Стандартные числовые типы в большинстве языков программирования могут содержать лишь конечный набор
значений, например от `0` до `255`. Когда результат арифметической операции выходит за эти
пределы он берется по модулю `256`. Обычно это не то что программист задумал и такие операции
приводят к ошибкам. В этой задаче предлагается верифицировать, что все переменные на протяжении всей
работы программы имеют значения меньше `256`.
-/

-- Чтобы рассуждать о промежуточных состояниях, нам понадобится small-step семантика
inductive SmallStep : Stmt × State → Stmt × State → Prop where
  | assign (x a s) :
    SmallStep (Stmt.assign x a, s) (Stmt.skip, Function.update s x (a s))
  | seqStep (S S' T s s') (hS : SmallStep (S, s) (S', s')) :
    SmallStep (S; T, s) (S'; T, s')
  | seqSkip (T s) :
    SmallStep (Stmt.skip; T, s) (T, s)
  | ifTrue (B S T s) (hcond : B s) :
    SmallStep (Stmt.ifThenElse B S T, s) (S, s)
  | ifFalse (B S T s) (hcond : ¬ B s) :
    SmallStep (Stmt.ifThenElse B S T, s) (T, s)
  | whileDo (B S s) :
    SmallStep (Stmt.whileDo B S, s)
      (Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip, s)

infixr:100 " ⇒ " => SmallStep

infixr:100 " ⇒* " => ReflTransGen SmallStep

/-- Напишите свойство, которое означает что все переменные в
состоянии `s` имеют значения меньше `256`. -/
def StateBounded (s : State) : Prop :=
  sorry

/-- Назовем программу ограниченной если она, начиная работу в состоянии `fun _ ↦ 0`
(все переменные равны 0), всегда остается в ограниченном состоянии. При этом мы не
требуем чтобы программа завершалась. -/
def ProgramBounded (S : Stmt) : Prop :=
  ∀ T t, (S, fun _ ↦ 0) ⇒* (T, t) → StateBounded t

/- Для программ без циклов доказывать/опровергать ограниченность можно
вручную. -/

def goodIf : Stmt :=
  .ifThenElse (fun _ => false) (
    .assign "x" 300
  ) (
    .assign "y" 30
  )

/-- Докажите ограниченность программы `goodIf`. -/
example : ProgramBounded goodIf := by
  sorry

def evilIf : Stmt :=
  .assign "x" 130;
  .ifThenElse (fun s => s "x" < 138) (
    .assign "x" (fun s => s "x" * 2)
  ) (
    .skip
  )

/-- Опровергните ограниченность программы `evilIf`. -/
example : ¬ ProgramBounded evilIf := by
  sorry

/- С циклами ситуация усложняется.

Например, программа
```py
x = 14
while True:
  if x < 64:
    x = x * 3 + 1
  else:
    x = x // 2
```
ограничена. Но вручную следуя за вычислением программы это показать невозможно,
потому что цикл бесконечный.

В таких ситуациях используют инварианты (еще такая техника называется
коиндукцией). Суть техники следующая:
1. Пусть есть некоторое свойство конфигураций `P`. Конфигурации обладающие этим
  свойством мы считаем хорошими. (В нашем случае `P = StateBounded`.)
  И пусть стартовая конфигурация хорошая.
2. Мы хотим доказать что на протяжении всей жизни программы конфигурации остаются
  хорошими.
3. Мы придумываем новое свойство `M` (т.н. инвариант) со следующими свойствами:
  - Из `M (S, s)` следует `P (S, s)`, т.е. `M` сужает `P`.
  - `M` выполняется для стартовой конфигурации.
  - Самое важное: если `M (S, s)` и `(S, s) ⇒ (S', s')`, то `M (S', s')`, то есть `M` сохраняется
    при переходах.
4. Тогда из последних двух свойств следует что на протяжении всей жизни программы конфигурации
  удовлетворяют свойству `M`. А значит они удовлетворяют и свойству `P` (по первому свойству).
-/

/-- Абстрактный вариант техники выше. `α` это множество конфигураций. `R` это отношение перехода. -/
theorem coinduction {α : Type} {R : α → α → Prop} {P : α → Prop} (M : α → Prop)
    {c₀ : α}
    (h₁ : ∀ c, M c → P c)
    (h₂ : M c₀)
    (h₃ : ∀ c c', M c → R c c' → M c') :
    ∀ c, ReflTransGen R c₀ c → P c := by
  suffices ∀ c, ReflTransGen R c₀ c → M c by
    grind
  intro c hc
  clear h₁
  induction hc with
  | refl => assumption
  | tail => grind

/--
```py
while True:
  if x < 64:
    x = x * 3 + 1
  else:
    x = x // 2
```
-/
def goodLoop : Stmt :=
  .whileDo (fun _ => true) (
    .ifThenElse (fun s => s "x" < 64) (
      .assign "x" (fun s => s "x" * 3 + 1)
    ) (
      .assign "x" (fun s => s "x" / 2)
    )
  )

/-- Давайте придумаем инвариант для программы `goodLoop` сохраняющий ограниченность.

Здесь все банально: мы будем просто делать перебор случаев: `GoodLoopInvariant (S, s)` верен если
1. S = goodLoop, s "x" < 256
2. S = тело цикла, s "x" < 256
3. S = первая ветвь if, s "x" < 64
4. S = вторая ветвь if, s "x" < 256
и так далее.

Дальше мы нам останется доказать что на каждом шаге программы мы переходим из одного случая в
другой, что из всех случаев следует ограниченность, и что стартовая конфигурация хорошая.
-/

/- Для удобства вынесем части программы в отдельные определения. -/
def tBranch : Stmt :=
  .assign "x" (fun s => s "x" * 3 + 1)
def fBranch : Stmt :=
  .assign "x" (fun s => s "x" / 2)
def body : Stmt :=
  .ifThenElse (fun s => s "x" < 64) tBranch fBranch

-- проверим себя
example : goodLoop = .whileDo (fun _ => true) body := by rfl

/-- Определим вспомогательное свойство. -/
def boundedX (s : State) (n : ℕ) : Prop := s "x" < n ∧ ∀ v, v ≠ "x" → s v = 0

/-- Из него следует ограниченность. -/
theorem boundedX_bounded {s n} (hs : boundedX s n) (hn : n ≤ 256) : StateBounded s := by
  simp [StateBounded]
  intro var
  by_cases hvar : var = "x"
  · simp [boundedX] at hs
    grind
  · simp [boundedX] at hs
    grind

/-- Определим инвариант перебором случаев. Заполните `sorry` для верхних границ на переменную
`x` в каждом случае. -/
inductive GoodLoopInvariant : Stmt × State → Prop where
| loop₁ (s) (hs : boundedX s sorry) :
  GoodLoopInvariant (goodLoop, s)
| loop₂ (s) (hs : boundedX s sorry) :
  GoodLoopInvariant (.ifThenElse (fun _ => true) (body; goodLoop) Stmt.skip, s)
| body (s) (hs : boundedX s sorry) :
  GoodLoopInvariant (body; goodLoop, s)
| tBranch (s) (hs : boundedX s sorry) :
  GoodLoopInvariant (tBranch; goodLoop, s)
| fBranch (s) (hs : boundedX s sorry) :
  GoodLoopInvariant (fBranch; goodLoop, s)
| loop₃ (s) (hs : boundedX s sorry) :
  GoodLoopInvariant (Stmt.skip; goodLoop, s)

/- Теперь докажите три необходимых свойства: -/

theorem goodLoopInvariant_start : GoodLoopInvariant (goodLoop, fun _ ↦ 0) := by
  sorry

theorem goodLoopInvariant_bounded {S s} (h : GoodLoopInvariant (S, s)) :
    StateBounded s := by
  sorry

theorem goodLoopInvariant_step {S S' s s'} (h : GoodLoopInvariant (S, s))
    (h_step : SmallStep (S, s) (S', s')) :
    GoodLoopInvariant (S', s') := by
  sorry

/-- Теперь можно доказать ограниченность программы `goodLoop`. -/
example : ProgramBounded goodLoop := by
  sorry


/--
```py
x = 1
i = 0
while i < 10:
  x = x * 2
  i = i + 1
```
-/
def evilLoop : Stmt :=
  .assign "x" 1;
  .assign "i" 0;
  .whileDo (fun s => s "i" < 10) (
    .assign "x" (fun s => s "x" * 2);
    .assign "i" (fun s => s "i" + 1)
  )

/-- Опровергните ограниченность программы `evilLoop`. Здесь инварианты не помогут, зато
можно доказать вспомогательные simp-леммы для small-step семантики и заставить `simp`
вычислить программу до некоторого неограниченного состояния. -/
example : ¬ ProgramBounded evilLoop := by
  sorry
