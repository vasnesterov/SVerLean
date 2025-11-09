import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Relation

open Relation

set_option linter.hashCommand false

/- # Задача 1. Неопределенные переменные

Реализуйте deep embedding языка WHILE со следующими ограничениями:
1. В правой части присвоения могут стоять только арифметические выражения
  с операциями `+`, `-`, `*`, нумералами и переменными.
  Нумералы представляйте в виде строк, проверять что они состоят только из цифр
  в этой задаче не нужно.
2. В условиях `if-then-else` и `while` могут стоять булевы выражения,
  составленные из констант `true`, `false`, булевых операций `&&`, `||`, `!`,
  и выражений вида `x == y`, `x < y`, `x <= y`,
  где `x` и `y` - арифметические выражения.
-/

abbrev State := String → ℕ

inductive Stmt : Type where
| skip       : Stmt
-- и так далее

/-- Напишите функцию которая проверяет что программа никогда не обращается к переменным которые
не были объявлены. Здесь мы считаем что переменная `x` была объявлена если выше в коде хоть где-то
есть присвоение `x := ...`. См. например пример 5 ниже. Функция должна возвращать `true` если
некорректных обращений нет. -/
def checkUndefined (s : Stmt) : Bool :=
  sorry

/- Протестируйте `checkUndefined` на следующих программах:

1. Корректна:
  skip

2. Корректна:
  x := 24

3. Некорректна:
  x := x

4. Корректна:
  x := 24
  x := x

5. Корректна:
  x := 10
  if x == x then
    y := x
  else
    skip
  x := y

6. Некорректна:
  x := 10
  if x == x then
    y := x
  else
    z := y

7. Некорректна:
  x := 10
  while x > 11 do
    x := y

8. Некорректна:
  while x < 10 do
    skip
-/

/- # Задача 2. Время работы

В этой задаче мы расширим big-step семантику добавив возможность рассуждать о том, за
сколько шагов программа завершается.
-/

namespace Problem2

abbrev State := String → ℕ

inductive Stmt : Type where
  | skip       : Stmt
  | assign     : String → (State → ℕ) → Stmt
  | seq        : Stmt → Stmt → Stmt
  | ifThenElse : (State → Bool) → Stmt → Stmt → Stmt
  | whileDo    : (State → Bool) → Stmt → Stmt

infixr:90 "; " => Stmt.seq

/-- `BigStep (S, s) t k` означает что программа `S`, начиная в состоянии `s`,
приходит в состояние `t` за `k` шагов. Мы используем нотацию `(S, s) ⟹[k] t`. -/
inductive BigStep : Stmt × State → State → ℕ → Prop where
  -- `skip` занимает 0 шагов
  | skip (s) :
    BigStep (Stmt.skip, s) s 0
  -- `assign` 1 шаг
  | assign (x a s) :
    BigStep (Stmt.assign x a, s) (Function.update s x (a s)) 1
  -- Если `S` занимает `n` шагов, а `T` - `m` шагов, то `S; T` - `n + m` шагов
  | seq (S T s t u n m) (hS : BigStep (S, s) t n) (hT : BigStep (T, t) u m) :
    BigStep (S; T, s) u (n + m)
  -- Если `S` занимает `n` шагов, и `cond = true`, то `if cond then S else T`
  -- занимает `n + 1` шаг (интуиция: 1 шаг на проверку условия)
  | ifTrue (B S T s t n) (hcond : B s) (hbody : BigStep (S, s) t n) :
    BigStep (Stmt.ifThenElse B S T, s) t (n + 1)
  -- Аналогично пункту выше
  | ifFalse (B S T s t n) (hcond : ¬ B s) (hbody : BigStep (T, s) t n) :
    BigStep (Stmt.ifThenElse B S T, s) t (n + 1)
  -- Если `cond = true` и `S` занимает `n` шагов, и оставшиеся итерации - `m` шагов
  -- то `while cond do S` занимает `n + m + 1` шаг
  | whileTrue (B S s t u n m) (hcond : B s) (hbody : BigStep (S, s) t n)
      (hrest : BigStep (Stmt.whileDo B S, t) u m) :
    BigStep (Stmt.whileDo B S, s) u (n + m + 1)
  -- Если `cond = false` то цикл `while cond do S` занимает `1` шаг
  | whileFalse (B S s) (hcond : ¬ B s) :
    BigStep (Stmt.whileDo B S, s) s 1

notation:110 Ss " ⟹[" n "] " t => BigStep Ss t n

/-- Вспомогательный предикат, означающий что программа `S`, начиная в состоянии `s`,
приходит в состояние `t` за _не более чем_ `n` шагов. -/
def BigStepLE (Ss : Stmt × State) (t : State) (n : ℕ) : Prop :=
  ∃ k ≤ n, Ss ⟹[k] t

notation:110 Ss " ⟹[≤" n "] " t => BigStepLE Ss t n

/-- Вспомогательный предикат, означающий что программа `S`, начиная в
состоянии `s`, завершается за не более чем `n` шагов. -/
def HaltsIn (S : Stmt) (s : State) (n : ℕ) : Prop :=
  ∃ t, (S, s) ⟹[≤n] t

/- Докажем основные свойства `BigStepLE` и `HaltsIn`. Часть доказана за вас, часть докажите сами. -/

theorem BigStepLE.skip (s n) :
    (Stmt.skip, s) ⟹[≤n] s := by
  use 0
  simp
  constructor

theorem BigStepLE.assign (x a s n) (h : 1 ≤ n) :
    (Stmt.assign x a, s) ⟹[≤n] (Function.update s x (a s)) := by
  use 1, h
  exact BigStep.assign x a s

theorem BigStepLE.seq (S T s t u n m k)
    (hS : (S, s) ⟹[≤n] t) (hT : (T, t) ⟹[≤m] u) (hk : n + m ≤ k) :
    (S; T, s) ⟹[≤k] u := by
  obtain ⟨n', hn', hSn'⟩ := hS
  obtain ⟨m', hm', hTm'⟩ := hT
  use n' + m'
  constructor
  · omega
  · apply BigStep.seq (n := n') (m := m') <;> assumption

theorem BigStepLE.ifTrue (B S T s t n m)
    (hcond : B s) (hbody : (S, s) ⟹[≤n] t) (hm : n + 1 ≤ m) :
    (Stmt.ifThenElse B S T, s) ⟹[≤m] t := by
  sorry

theorem BigStepLE.ifFalse (B S T s t n m)
    (hcond : ¬ B s) (hbody : (T, s) ⟹[≤n] t) (hm : n + 1 ≤ m) :
    (Stmt.ifThenElse B S T, s) ⟹[≤m] t := by
  sorry

theorem BigStepLE.whileTrue (B S s t u n m k)
    (hcond : B s) (hbody : (S, s) ⟹[≤n] t) (hrest : (Stmt.whileDo B S, t) ⟹[≤m] u)
    (hk : n + m + 1 ≤ k) :
    (Stmt.whileDo B S, s) ⟹[≤k] u := by
  obtain ⟨n', hn', hbody'⟩ := hbody
  obtain ⟨m', hm', hrest'⟩ := hrest
  use n' + m' + 1
  constructor
  · omega
  · apply BigStep.whileTrue (n := n') (m := m') <;> assumption

theorem BigStepLE.whileFalse (B S s n) (hcond : ¬ B s) (hn : 1 ≤ n) :
    (Stmt.whileDo B S, s) ⟹[≤n] s := by
  use 1
  constructor
  · exact hn
  · apply BigStep.whileFalse
    assumption

theorem HaltsIn_assign (x a s n) (hn : 1 ≤ n) :
    HaltsIn (Stmt.assign x a) s n := by
  use Function.update s x (a s), 1, by omega
  apply BigStep.assign

theorem HaltsIn_seq (S T s t n m k) (hS : (S, s) ⟹[≤n] t) (hT : HaltsIn T t m)
    (hk : n + m ≤ k) :
    HaltsIn (S; T) s k := by
  sorry

theorem HaltsIn_ifTrue (B S T s n m) (hcond : B s) (hbody : HaltsIn S s n) (hm : n < m) :
    HaltsIn (Stmt.ifThenElse B S T) s m := by
  obtain ⟨t, hST⟩ := hbody
  use t
  apply BigStepLE.ifTrue (n := n) (m := m) <;> assumption

theorem HaltsIn_ifFalse (B S T s n m) (hcond : ¬ B s) (hbody : HaltsIn T s n) (hm : n < m) :
    HaltsIn (Stmt.ifThenElse B S T) s m := by
  obtain ⟨t, hST⟩ := hbody
  use t
  apply BigStepLE.ifFalse (n := n) (m := m) <;> assumption

theorem HaltsIn_whileTrue (B S s t n m k) (hcond : B s) (hbody : (S, s) ⟹[≤n] t)
    (hrest : HaltsIn (Stmt.whileDo B S) t m) (hk : n + m + 1 ≤ k) :
    HaltsIn (Stmt.whileDo B S) s k := by
  sorry

theorem HaltsIn_whileFalse (B S s n) (hcond : ¬ B s) (hn : 0 < n) :
    HaltsIn (Stmt.whileDo B S) s n := by
  use s, 1, by omega
  apply BigStep.whileFalse
  assumption

theorem BigStepLE_mono (S s t n m) (h : n ≤ m) (hS : (S, s) ⟹[≤n] t) :
    (S, s) ⟹[≤m] t := by
  obtain ⟨k, hk, hS'⟩ := hS
  simp [BigStepLE]
  use k, by grind

theorem HaltsIn_mono {S s n m} (hS : HaltsIn S s n) (h : n ≤ m) :
    HaltsIn S s m := by
  obtain ⟨t, hST⟩ := hS
  use t
  apply BigStepLE_mono (n := n) (m := m) <;> assumption

/-- Программа проверяющая простоту числа `n ≥ 2`. -/
def isPrime (n : ℕ) : Stmt :=
  .assign "i" (fun _ => 2);
  .assign "result" (fun _ => 1);
  .whileDo (fun s => s "i" * s "i" ≤ n) (
    .ifThenElse (fun s => n % s "i" == 0) (
      .assign "result" (fun _ => 0)
    ) (
      .skip
    );
    .assign "i" (fun s => s "i" + 1)
  )

/-- Вспомогательная лемма для доказательства времени работы `isPrime`.

Подсказка: вместо тактики `induction` используйте ссылку на доказываемое утверждение
и докажите "корректность индукции" при помощи `decreasing_by`. -/
theorem isPrime_sqrt_time_aux (n i result : ℕ) :
    HaltsIn (.whileDo (fun s => s "i" * s "i" ≤ n) (
      .ifThenElse (fun s => n % s "i" == 0) (
        .assign "result" (fun _ => 0)
      ) (
        .skip
      );
      .assign "i" (fun s => s "i" + 1)
    )) (fun x => match x with | "i" => i | "result" => result | _ => 0)
    (4 * (n.sqrt + 1 - i) + 1) := by
  sorry
termination_by n.sqrt + 1 - i

/-- Докажите, что `isPrime n` требует `O(√n)` операций. -/
theorem isPrime_sqrt_time : ∃ A B, ∀ n,
    HaltsIn (isPrime n) (fun _ => 0) (A * n.sqrt + B) := by
  sorry

end Problem2

/- # Задача 3. Доказательство неостановки

Используя big-step семантику можно доказывать что данная программа останавливается.
Но доказывать обратное в ней трудно.

В этой задаче предлагается доказать неостановку программы при помощи следующего
простого наблюдения: если `(S, s) ⇒+ (S, s)` (в терминах small-step семантики), т.е.
из состояния `s` через некоторое положительное число шагов программа опять
переходит в состояние `s`, то она точно не остановится.
-/

namespace Problem3

abbrev State := String → ℕ

inductive Stmt : Type where
  | skip       : Stmt
  | assign     : String → (State → ℕ) → Stmt
  | seq        : Stmt → Stmt → Stmt
  | ifThenElse : (State → Bool) → Stmt → Stmt → Stmt
  | whileDo    : (State → Bool) → Stmt → Stmt

infixr:90 "; " => Stmt.seq

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

infixr:100 " ⇒+ " => TransGen SmallStep

infixr:100 " ⇒* " => ReflTransGen SmallStep

@[simp]
theorem SmallStep_skip_final (s C) : ¬ (Stmt.skip, s) ⇒ C := by
  intro h
  cases h

@[simp]
theorem SmallStep_skip_final' (s T t) : (Stmt.skip, s) ⇒* (T, t) ↔ T = .skip ∧ s = t where
  mp h := by
    obtain h | ⟨_, h, _⟩ := ReflTransGen.cases_head h
    · grind
    · simp at h
  mpr h := by
    rw [h.1, h.2]

/-- Программа `program` начиная в состоянии `state` завершается, если она переходит в конфигурацию
`(.skip, _)` за конечное число шагов. -/
def Halts (program : Stmt) (state : State) : Prop :=
  ∃ state', (program, state) ⇒* (.skip, state')

/- В этой задаче мы будем широко использовать свойства отношения `⇒` (а так же `⇒+` и `⇒*`).

Используйте loogle и документацию Lean для поиска нужных теорем.

Для ReflTransGen и TransGen:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Relation.html#Relation.ReflTransGen

Скорее всего понадобятся:
* `Relation.TransGen.head'_iff`
* `TransGen.head'`
* `ReflTransGen.head`
* `ReflTransGen.single`
* `ReflTransGen.refl`
* `ReflTransGen.trans`
* `TransGen.trans_right`
* Индуктивный принцип `ReflTransGen.head_induction_on` (для `induction .. using`)
-/

/-- Первое что нам нужно: отношение `⇒` _функционально_, то есть если
`a ⇒ b` и `a ⇒ c`, то `b = c`. То есть `⇒` задает частичную функцию.
Если смотреть на отношение как на граф, то это свойство означает что из любой вершины
выходит не более одного ребра. -/
theorem SmallStep_RightUnique : Relator.RightUnique SmallStep := by
  intro a b c hab hac
  induction hab generalizing c <;> cases hac <;> grind [SmallStep_skip_final]

/- Нам потребуются два свойства функциональных отношений: -/

/-- Если `R` - функциональное отношение, и `a R+ a` то `a R* b` влечет `b R+ a`.
Интуиция: если выходя из `a` мы попадаем в цикл и возвращаемся в `a`, то из любой вершины `b` из
цикла можно попасть в `a`. -/
theorem RightUnique_TransGen_self_TransGen_comm {α : Type} {R : α → α → Prop} {a b : α}
    (hR : Relator.RightUnique R) (h_loop : TransGen R a a) (hab : ReflTransGen R a b) :
    TransGen R b a := by
  sorry -- бонус

/-- Если `⇒` - функциональное отношение, и `a ⇒* b` и `a ⇒* c`, то либо `b ⇒* c`, либо
`c ⇒* b`.
Интуиция: если есть путь из `a` в `b` и в `c`, то либо `b` лежит на пути из `a` в `c`,
либо `c` лежит на пути из `a` в `b`. -/
theorem RightUnique_ReflTransGen_semiconnected {α : Type} {R : α → α → Prop} {a b c : α}
    (hR : Relator.RightUnique R) (hab : ReflTransGen R a b) (hac : ReflTransGen R a c) :
    ReflTransGen R b c ∨ ReflTransGen R c b := by
  sorry -- бонус

/-- Используя свойства выше, докажите следующее свойство: -/
theorem Halts_equiv {S T : Stmt} {s t : State}
    (hST : (S, s) ⇒* (T, t)) :
    Halts S s ↔ Halts T t where
  mp hS := by
    sorry
  mpr hT := by
    sorry

/-- Если программа `S` зацикливается (возвращается в исходное состояние), то она не останавливается.
Используйте `RightUnique_TransGen_self_TransGen_comm`. -/
theorem loop_not_Halts {S : Stmt} {s : State}
    (h_loop : (S, s) ⇒+ (S, s)) :
    ¬ Halts S s := by
  sorry

/-- Обощение предыдущего. С использованием доказанного выше, доказательство должно быть
коротким (≤ 3 строк). -/
theorem has_loop_not_Halts {S T : Stmt} {s t : State}
    (h1 : (S, s) ⇒* (T, t))
    (h2 : (T, t) ⇒+ (T, t)) :
    ¬ Halts S s := by
  sorry

/- Примените доказанное выше к следующим программам: -/

def easyLoop : Stmt := .whileDo (fun _ => true) .skip

theorem easyLoop_not_Halts (state : State) : ¬ Halts easyLoop state := by
  sorry

def hardLoop : Stmt :=
  .assign "x" (fun _ => 0);
  .whileDo (fun s => s "x" < 3) (
    .assign "x" (fun s => next (s "x"))
  )
where
  next (x : ℕ) : ℕ := 1 + 2 * x - x ^ 2

theorem hardLoop_not_Halts (state : State) : ¬ Halts hardLoop state := by
  sorry

/- **Бонус**: В общем случае программа может зацикливаться при этом не возвращаясь в одно и то же
состояние несколько раз. Чтобы учесть такие ситуации обобщим предыдущее так.
Пусть `P : State → Prop` - предикат, который
1. Верен для состояния `s₀`.
2. Для любого состояния `s`, если `P s` то найдется `t` такое что `(S, s) ⇒+ (S, t)` и
  для `t` снова верно `P`. Неформально говоря, если мы стартуем в состоянии в котором верно `P`,
  то мы неизбежно снова возвращаемся в (возможно другое) состояние в котором опять верно `P`.
Тогда программа обязана "заходить" во множество `{s | P s}` бесконечное число раз, и не
остановится. Формализуйте это, заполнив `sorry` ниже.
-/

theorem loop_not_Halts' {S : Stmt} {s : State} {P : State → Prop}
    (h_init : P s) (h_loop : ∀ s, P s → ∃ t, P t ∧ (S, s) ⇒+ (S, t)) :
    ¬ Halts S s := by
  sorry

theorem has_loop_not_Halts' {S T : Stmt} {s t : State}
    {P : State → Prop}
    (h_loop : ∀ s, P s → ∃ t, P t ∧ (T, s) ⇒+ (T, t))
    (h1 : (S, s) ⇒* (T, t))
    (h2 : P t) :
    ¬ Halts S s := by
  sorry

def endlessInc : Stmt :=
  .assign "x" 10;
  .whileDo (fun s => s "x" > 5) (
    .assign "x" (fun s => s "x" + 1)
  )

theorem endlessInc_not_Halts (state : State) : ¬ Halts endlessInc state := by
  sorry

/-- **Бонус**: Верно и обратное: если программа не останавливается, она зацикливается
в нашем обобщенном смысле. -/
theorem not_Halts_has_loop (S : Stmt) (s : State) (h : ¬ Halts S s) :
    ∃ (P : State → Prop) (T : Stmt) (t : State),
      (∀ t, P t → ∃ t', (T, t) ⇒+ (T, t') ∧ P t') ∧ (S, s) ⇒* (T, t) ∧ P t := by
  sorry

end Problem3
