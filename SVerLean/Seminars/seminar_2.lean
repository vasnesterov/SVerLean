import Std.Data.HashMap.Basic

/-
# Семинар 2.
-/

/- ## Задача 1. Быстрое возведение в степень -/

/--
Реализуйте быстрое возведение в степень, вычисляющее `m ^ n` за `O(log n)`.

Для справки код на Python:
```py
  def fastPow(m, n):
    if n == 0:
      return 1
    half = fastPow(m, n // 2)
    if n % 2 == 0:
      return half * half
    else
      return half * half * m
```

Укажите убывающую меру в `termination_by`
Если Lean не справится сразу доказать что она действительно убывает на
рекурсивных вызовах, попробуйте дописать `decreasing_by all_goals grind`
-/
def fastPow (m n : Nat) : Nat :=
  sorry

#guard fastPow 2 0 == 1
#guard fastPow 2 4 == 16
#guard fastPow 2 15 == 32768

/-- Тип для арифметических выражений. Любое выражение это -/
inductive ArithExpr : Type
/-- Либо число -/
| num : Int → ArithExpr
/-- Либо переменная -/
| var : String → ArithExpr
/-- Либо сумма двух выражений -/
| add : ArithExpr → ArithExpr → ArithExpr
/-- Либо произведение двух выражений -/
| mul : ArithExpr → ArithExpr → ArithExpr
/-- Либо выражение с противоположным знаком -/
| neg : ArithExpr → ArithExpr
deriving BEq

/--
## Разминка

Выразите вычитание арифметических выражений через конструкторы.
-/
def ArithExpr.sub (e₁ e₂ : ArithExpr) : ArithExpr :=
  sorry

/--
# Задача 2. Вычисление выражений

Напишите функцию для вычисления выражения при заданном значении переменных.
Значения переменных задаются при помощи аргумента `env`, который является функцией, отображающей
имя переменной в её значение.
-/
def ArithExpr.eval (e : ArithExpr) (env : String → Int) : Int :=
  sorry

/- Введем несколько выражений для тестирования. -/

/-- 1 + x -/
def expr₁ : ArithExpr := .add (.num 1) (.var "x")
/-- -2 * y -/
def expr₂ : ArithExpr := .mul (.num (-2)) (.var "y")
/-- 1 + x + 2 * y -/
def expr₃ : ArithExpr := .add expr₁ expr₂.neg

#guard expr₁.eval (fun _ => 3) == 4
#guard expr₂.eval (fun _ => 3) == -6
#guard expr₃.eval (fun name => match name with | "x" => 3 | "y" => -2 | _ => 0) == 0

/-
## Задача 3. Упрощение нумералов в выражениях

Напишите функцию `simplifyNum` которая упрощает выражение, заменяя числовые подвыражения на их значения.
  Например `x * (1 + 2 * 3) + (5 - 4)` должно упроститься до `x * 7 + 1`.
-/

def simplifyNum (e : ArithExpr) : ArithExpr :=
  sorry

#guard simplifyNum (.add (.mul (.var "x") (.add (.num 1) (.mul (.num 2) (.num 3)))) (.sub (.num 5) (.num 4))) ==
  .add (.mul (.var "x") (.num 7)) (.num 1)

/-
## Задача 4. Структурная положительность

Выражение называется структурно положительным когда его положительность "очевидна" синтаксически.
Например, выражение `e₁ + e₂` положительно при условии что `e₁` и `e₂` положительны, и в этом случае
нам не нужно "залезать внутрь" выражений `e₁` и `e₂`, достаточно знать что они положительны.
Выражение `x² + y² - 2 x y + 1` положительно, ведь оно равно `(x - y)² + 1`,
однако структурно положительным оно не является, потому что `- 2 x y` может быть отрицательным.

Напишите функцию `isStructurallyPositive` которая проверяет,
является ли выражение структурно положительным и `isStructurallyNegative` которая проверяет,
является ли выражение структурно отрицательным.

Подсказка: используйте `mutual` для взаимной рекурсии.

В этой задаче мы считаем что переменные принимают только положительные значения.
-/

def isStructurallyPositive (e : ArithExpr) : Bool :=
  sorry

def isStructurallyNegative (e : ArithExpr) : Bool :=
  sorry

#guard !(isStructurallyPositive expr₂)
#guard isStructurallyPositive expr₃

/- ## Задача 5. Камень-ножницы-бумага -/

/-- Варианты ходов в игре "камень-ножницы-бумага" -/
inductive RSP
| rock
| scissors
| paper

/-- Получив ходы соперников `move₁` и `move₂` вычисляет счёт за раунд: +1 значит что выиграл первый игрок,
-1 значит что выиграл второй. -/
def score (move₁ move₂ : RSP) : Int :=
  match move₁, move₂ with
  | .rock, .scissors => 1
  | .scissors, .paper => 1
  | .paper, .rock => 1
  | .rock, .rock => 0
  | .scissors, .scissors => 0
  | .paper, .paper => 0
  | .scissors, .rock => -1
  | .paper, .scissors => -1
  | .rock, .paper => -1

/-- Стратегия игры.

Любую стратегию можно себе мыслить как программу (возможно, очень сложную) у которой есть внутреннее
состояние `q : Q` (где `Q` - какой-то тип состояний, свой для каждой программы), которая действует
следующим образом:
1. Находясь в состоянии `q : Q`, она делает ход `action q : RSP`
2. Затем увидев ход соперника `opponentMove` она переходит в новое
  состояние `nextState q opponentMove : Q` и игра продолжается

Примеры ниже должны прояснить суть определения.

P.S.: на самом деле такая модель описывает только детерминированные стратегии, которые не
используют случайность. Но это все равно очень широкий класс стратегий! -/
structure Strategy (Q : Type) where
  initState : Q
  action : Q → RSP
  nextState : Q → RSP → Q

/-- Стратегия которая всегда ходит камнем.

Этой стратегии достаточно одного состояния (поэтому `Q = Unit`), находясь
в котором она ходит камнем и остается в этом состоянии. -/
def alwaysRock : Strategy Unit where
  initState := ()
  action _ := .rock
  nextState _ _ := ()

/-- Стратегия, которая чередует камень и бумагу.

Этой стратегии нужно два состояния (`Q = Bool`), между которыми она переходит туда-обратно.
Находясь в состоянии `true` она ходит камнем, находясь в состоянии `false` - бумагой.
-/
def interleaveRockPaper : Strategy Bool where
  initState := false
  action b := if b then .rock else .paper
  nextState b _ := ! b

/-- Стратегия, которая копирует предыдущий ход соперника.

Поймите сами как она работает.
-/
def copyOpponent : Strategy RSP where
  initState := .rock
  action q := q
  nextState _ opponentMove := opponentMove

/-- Напишите функцию которая играет двумя стратегиями друг против друга `nRounds` раундов и
выдает общий счет. -/
def play {Q₁ Q₂ : Type} (strategy₁ : Strategy Q₁) (strategy₂ : Strategy Q₂)
    (nRounds : Nat) : Int :=
  sorry

#guard play alwaysRock alwaysRock 10 == 0
#guard play alwaysRock interleaveRockPaper 10 == -5
#guard play alwaysRock copyOpponent 10 == 0
#guard play copyOpponent copyOpponent 10 == 0

/-- Напишите функцию, которая принимает на вход стратегию соперника и
выдает стратегию, которая побеждает против неё во всех раундах. -/
def bestResponse {Q : Type} (opponent : Strategy Q) : Strategy Q where
  initState := sorry
  action q := sorry
  nextState q _ := sorry

#guard play alwaysRock (bestResponse alwaysRock) 10 == -10
#guard play interleaveRockPaper (bestResponse interleaveRockPaper) 10 == -10
#guard play copyOpponent (bestResponse copyOpponent) 10 == -10
