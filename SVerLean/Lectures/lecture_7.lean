import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Relation

open Relation

set_option linter.hashCommand false

/-
## Минималистичный императивный язык

Состояние `s` — это функция из имён переменных в значения (`String → ℕ`).

__WHILE__ — минималистичный императивный язык со следующей грамматикой:

    S  ::=  skip                 -- пропуск (no-op)
         |  x := a               -- присваивание
         |  S; S                 -- последовательная композиция
         |  if B then S else S   -- условный оператор
         |  while B do S         -- цикл while

где `S` обозначает программу (statement),
`x` — переменная, `a` — арифметическое выражение,
а `B` — булево выражение.
-/

abbrev State := String → ℕ

inductive Stmt : Type where
  | skip       : Stmt
  | assign     : String → (State → ℕ) → Stmt
  | seq        : Stmt → Stmt → Stmt
  | ifThenElse : (State → Bool) → Stmt → Stmt → Stmt
  | whileDo    : (State → Bool) → Stmt → Stmt

infixr:90 "; " => Stmt.seq

-- считаем сумму чисел от 0 до 9
def sum10 : Stmt :=
  .assign "i" (fun s => 0);
  .assign "sum" (fun s => 0);
  .whileDo (fun s => (s "i") < 10)
    (.assign "sum" (fun s => s "sum" + s "i"))

-- бесконечный цикл
def loop : Stmt :=
  .whileDo (fun s => True) .skip

namespace hidden

/-

# Deep embedding vs Shallow embedding

При погружении любого синтаксиса (языка программирования)
в Lean у нас есть две возможности:

* Shallow embedding: переиспользовать типы Lean как в примере выше:
  ℕ, Prop
* Deep embedding: работать напрямую с синтаксисом и представлять
объекты в виде синтаксических деревьев

В примере выше мы используем shallow embedding для операций и deep
embedding для натуральных чисел и Prop.

C одной стороны работать с shallow embedding проще потому что мы
можем переиспользовать определения и теоремы для существующих типов.

С другой стороны это сложнее потому что мы теряем контроль над
частью программы. Например программа для вычисления 10го числа
Фибоначчи может выглядеть так:
-/
def fib (n : ℕ) := match n with
  | m + 2 => fib m + fib (m + 1)
  | _ => 1

def cheatFib10 : Stmt := .assign "result" (fun _ ↦ fib 10)
/-
т.е. наши программы благодаря shallow embedding получают доступ ко
всей машинерии Lean.

Для deep embedding нам бы стоило сделать как-то так:
-/
inductive NatExpr
  | num (n : String)
  | var (x : String)
  | add (x y : NatExpr)
  | sub (x y : NatExpr)
  -- и так далее

inductive BoolExpr
  | t
  | f
  | and (x y : BoolExpr)
  | or (x y : BoolExpr)
  -- и так далее

inductive Stmt : Type where
  | skip       : Stmt
  | assign     : String → NatExpr → Stmt
  | seq        : Stmt → Stmt → Stmt
  | ifThenElse : BoolExpr → Stmt → Stmt → Stmt
  | whileDo    : BoolExpr → Stmt → Stmt

/- Теперь программу для чисел Фибоначчи можно написать только
"честно": мы получили больше контроля.

В общем, чем глубже наше погружение тем больше наш контроль над
языком и тем больше свойств программ мы можем доказать. -/

end hidden

/- # Операционная семантика

Рассуждать о программах можно на разных "языках", которые по разному
отвечают на вопрос "что такое программа?"

Один из таких языков: операционная семантика.
В ней программа -- это нечто, что переходит из состояния в состояние.

В рамках операционной семантики существуют два основных варианта:
* small-step семантика
* big-step семантика
-/

/-
В __big-step семантике__ (также называемой __натуральной семантикой__)
суждения имеют вид `(S, s) ⟹ t`:

  Начинаясь в состоянии `s`, выполнение программы `S` завершается в состоянии `t`.

Пример:

    `(x := x + y; y := 0, [x ↦ 3, y ↦ 5]) ⟹ [x ↦ 8, y ↦ 0]`

Правила вывода:

    ——————————————— Skip
    (skip, s) ⟹ s

    ——————————————————————————— Assign
    (x := a, s) ⟹ s[x ↦ s(a)]

    (S, s) ⟹ t   (T, t) ⟹ u
    ——————————————————————————— Seq
    (S; T, s) ⟹ u

    (S, s) ⟹ t
    ————————————————————————————— If-True   if s(B) is true
    (if B then S else T, s) ⟹ t

    (T, s) ⟹ t
    ————————————————————————————— If-False   if s(B) is false
    (if B then S else T, s) ⟹ t

    (S, s) ⟹ t   (while B do S, t) ⟹ u
    —————————————————————————————————————— While-True   if s(B) is true
    (while B do S, s) ⟹ u

    ————————————————————————— While-False   if s(B) is false
    (while B do S, s) ⟹ s

Здесь `s(e)` обозначает значение выражения `e` в состоянии `s`,
а `s[x ↦ s(e)]` обозначает состояние, идентичное `s`, за исключением того,
что переменная `x` теперь содержит значение `s(e)`.

В Lean это суждение соответствует индуктивному предикату,
а правила вывода - конструкторам этого предиката.
-/

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

/- # Верификация конкретных программ

Пусть дана конкретная программа `S` и состояние `s`.
Как нам автоматически доказать что `(S, s) ⟹ t`?
Давайте заведем несколько `simp`-лемм для правил, и при помощи них будем
использовать `simp` как исполнитель программы.
-/

@[simp]
theorem BigStep_skip_iff (s t) :
    (Stmt.skip, s) ⟹ t ↔ s = t where
  mp h := by
    cases h
    rfl
  mpr h := by
    rw [h]
    constructor

@[simp]
theorem BigStep_assign_iff (x a s t) :
    (Stmt.assign x a, s) ⟹ t ↔ (t = Function.update s x (a s)) where
  mp h := by
    cases h
    rfl
  mpr h := by
    rw [h]
    constructor

@[simp]
theorem BigStep_seq_iff (S T s u) :
    (S; T, s) ⟹ u ↔ (∃ t, (S, s) ⟹ t ∧ (T, t) ⟹ u) where
  mp h := by
    cases h with
    | seq S T s t u hS hT =>
      use t
  mpr h := by
    obtain ⟨t, hS, hT⟩ := h
    constructor
    · exact hS
    · exact hT

@[simp]
theorem BigStep_if_iff (cond St Sf s t) :
    (Stmt.ifThenElse cond St Sf, s) ⟹ t ↔
    if cond s then (St, s) ⟹ t else (Sf, s) ⟹ t where
  mp h := by
    cases h with
    | ifTrue _ _ _ _ _ hcond hbody =>
      simp [hcond, hbody]
    | ifFalse _ _ _ _ _ hcond hbody =>
      simp [hcond, hbody]
  mpr h := by
    split_ifs at h with hcond
    · apply BigStep.ifTrue
      all_goals assumption
    · apply BigStep.ifFalse
      all_goals assumption

-- это `simp` не помечаем, иначе при вызове тактики `simp` будут
-- возникать бесконечные циклы. Но это можно обойти: см. ниже
theorem BigStep_while_iff (cond body s t) :
    (Stmt.whileDo cond body, s) ⟹ t ↔
    if cond s then (body; Stmt.whileDo cond body, s) ⟹ t else s = t where
  mp h := by
    cases h with
    | whileTrue _ _ _ u _ hcond hbody hrest =>
      simp [hcond]
      use u
    | whileFalse _ _ _ hcond =>
      simp [hcond]
  mpr h := by
    split_ifs at h with hcond
    · cases h with
      | seq _ _ _ u _ hbody hrest =>
      apply BigStep.whileTrue _ _ _ _ _ hcond hbody hrest
    · subst h
      apply BigStep.whileFalse
      assumption

/--
  ```py
  cnt = 3
  while cnt > 0:
    cnt -= 1
  ```
-/
def countdown : Stmt :=
  .assign "cnt" (fun _ => 3);
  .whileDo (fun state => state "cnt" > 0) (
    .assign "cnt" (fun state => state "cnt" - 1)
  )

/-- `countdown` завершается в состоянии `[cnt = 0]`. -/
theorem countdown_BigStep_zero :
    (countdown, fun _ ↦ 0) ⟹ (fun _ ↦ 0) := by
  simp only [countdown]
  -- комбинатор `first | tac₁ | tac₂` применяет тактику `tac₁`,
  -- и если она вернула ошибку, применяет тактику `tac₂`.
  -- комбинатор `repeat tac` применяет тактику `tac`
  -- пока она применяется без ошибок
  repeat (first | simp | rw [BigStep_while_iff])

-- Примечание: `repeat (first | simp | rw [BigStep_while_iff])`
-- сносно работает для крошечных программ. Но по-хорошему стоило бы
-- написать отдельную тактику для этой цели.

-- big-step семантика детерминирована. Доказательство в семинаре
theorem BigStep_deterministic {S s l r} (hl : (S, s) ⟹ l)
    (hr : (S, s) ⟹ r) :
    l = r := by
  sorry

/- ## Small-step семантика

Big-step семантика имеет следующие недостатки:

* не позволяет рассуждать о промежуточных состояниях;

* не позволяет выразить незавершаемость или чередование (например, для многопоточности).

__Small-step семантика__ (также называется __структурной операционной семантикой__)
решает эти проблемы.

В этой семантике используется суждение вида `(S, s) ⇒ (T, t)`:

    Начиная в состоянии `s`, выполнение одного шага программы `S`
    приводит к состоянию `t`, при этом дальнейшая программа,
    которую нужно исполнить, - это `T`.

Выполнение программы — это конечная или бесконечная
цепочка переходов `(S₀, s₀) ⇒ (S₁, s₁) ⇒ …`.

Пара `(S, s)` называется __конфигурацией__.
Она __финальная__, если не существует перехода вида `(S, s) ⇒ _`.

Пример:

      `(x := x + y; y := 0, [x ↦ 3, y ↦ 5])`
    `⇒ (skip; y := 0,       [x ↦ 8, y ↦ 5])`
    `⇒ (y := 0,             [x ↦ 8, y ↦ 5])`
    `⇒ (skip,               [x ↦ 8, y ↦ 0])`

Правила вывода:

    ————————————————————————————————— Assign
    (x := a, s) ⇒ (skip, s[x ↦ s(a)])

    (S, s) ⇒ (S', s')
    ———-——————————————————— Seq-Step
    (S; T, s) ⇒ (S'; T, s')

    ————————————————————— Seq-Skip
    (skip; S, s) ⇒ (S, s)

    ———————————————————————————————— If-True   if s(B) is true
    (if B then S else T, s) ⇒ (S, s)

    ———————————————————————————————— If-False   if s(B) is false
    (if B then S else T, s) ⇒ (T, s)

    ——————————————————————————————————————————————————————————————— While
    (while B do S, s) ⇒ (if B then (S; while B do S) else skip, s)

Нет правила для `skip` (почему?). -/

inductive SmallStep : Stmt × State → Stmt × State → Prop where
  | assign (x a s) :
    SmallStep (Stmt.assign x a, s) (Stmt.skip, Function.update s x (a s))
  | seq_step (S S' T s s') (hS : SmallStep (S, s) (S', s')) :
    SmallStep (S; T, s) (S'; T, s')
  | seq_skip (T s) :
    SmallStep (Stmt.skip; T, s) (T, s)
  | if_true (B S T s) (hcond : B s) :
    SmallStep (Stmt.ifThenElse B S T, s) (S, s)
  | if_false (B S T s) (hcond : ¬ B s) :
    SmallStep (Stmt.ifThenElse B S T, s) (T, s)
  | whileDo (B S s) :
    SmallStep (Stmt.whileDo B S, s)
      (Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip, s)

infixr:100 " ⇒ " => SmallStep

infixr:100 " ⇒* " => ReflTransGen SmallStep

theorem BigStep_iff_SmallStep (S s t) :
    (S, s) ⟹ t ↔ (S, s) ⇒* (Stmt.skip, t) := by
  sorry
