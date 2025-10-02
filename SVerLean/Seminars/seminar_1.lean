
variable {α β γ : Type}

/- # Задача 1. Термы

Замените `sorry` на абстрактные функции нужного типа, используя `fun`.
-/

def I : α → α :=
  sorry

def K : α → β → α :=
  sorry

def C : (α → β → γ) → β → α → γ :=
  fun f b a => f a b

def projFirst : α → α → α :=
  sorry

/- Give a different answer than for `projFst`. -/
def projSecond : α → α → α :=
  sorry

def someNonsense : (α → β → γ) → α → (α → γ) → β → γ :=
  sorry

/- # Задача 2. Prod -/

/-- Пример паттерн-матчинга для типа `Prod` -/
def pairAdd (p : Nat × Nat) : Nat :=
  match p with
  | (x, y) => x + y
  -- второй вариант того же паттерна: `(x, y)` -- это просто нотация для `Prod.mk a b`:
  -- | Prod.mk x y => x + y

/-- То же самое без паттерн-матчинга -/
def pairAdd' (p : Nat × Nat) : Nat :=
  p.fst + p.snd

/-- То же самое но с синтаксическим сахаром.
При "рассахаривании" это превращается в тело `pairAdd`. -/
def pairAdd'' : Nat × Nat → Nat :=
  fun (x, y) => x + y

/- Напишите этими тремя способами функцию которая меняет местами элементы пары. -/

def Prod.mySwap : sorry := sorry

def Prod.mySwap' : sorry := sorry

def Prod.mySwap'' : sorry := sorry

-- #eval Prod.mySwap (1, -1) -- expected: (-1, 1)

/- Реализуйте операцию "каррирования", т.е. превращения функции `f : α × β → γ` в `f : α → (β → γ)` и
обратную операцию. -/

def curry (f : α × β → γ) : α → (β → γ) :=
  sorry

def uncurry (f : α → (β → γ)) : α × β → γ :=
  sorry

/- # Задача 3. List -/

def sum (li : List Nat) : Nat :=
  match li with
  | [] => 0
  | List.cons head tail => head + sum tail

def collatz (n : Nat) : Nat :=
  if n == 0 then
    0
  else
    collatz (n / 2)
termination_by n
decreasing_by grind
    -- if n % 2 == 0 then
    --   collatz (n / 2)
    -- else
    --   collatz (3 * n + 1)

/--
Напишите функцию `myMap` которая поэлементно применяет функцию `f` к элементам списка, т.е.
`myMap [x, y, z, ...] = [f x, f y, f z, ...]`. Постарайтесь сделать ее как можно более полиморфной.

P.S.: в стандартной библиотеке такая операция называется `List.map`.
-/
def List.myMap : sorry := sorry

/--
Напишите функцию `myZip` которая соединяет в лист пар два листа `x : List α` и `y : List β` так что
`myZip [x₁, x₂, x₃, ...] [y₁, y₂, y₃, ...] = [(x₁, y₁), (x₂, y₂), (x₃, y₃), ...]`
-/
def List.myZip (xs : List α) (ys : List β) : List (α × β) :=
  match xs, ys with
  | x :: tail_x, y :: tail_y =>
    (x, y) :: tail_x.myZip tail_y
    --  (x, y) :: List.myZip tail_x tail_y
  | _, _ => []

#print List.myZip

/--
Напишите функцию `myCount` возвращающую количество элементов в листе, удовлетворяющих предикату `p`.
-/
def List.myCount : sorry := sorry

/--
Выразите длину листа через `List.myCount`
-/
def List.myLength {α : Type} (li : List α) : Nat :=
  sorry

/- # Задача 4. Nat -/

/-- Пример паттерн-матчинга для `Nat`. Любое натуральное число либо является нулем,
либо может быть представленно в виде `Nat.succ m = m + 1`.
`pred` вычисляет предыдущее натуральное число.
Если такого нет (т.е. `n = 0`), возвращает `0`. -/
def pred (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | Nat.succ m => m

/- Так же можно определить другие арифметические операции на натуральных числах. -/

/-- Вычитание на натуральных числах. Если `x < y` то возвращается ноль.
Пример одновременно показывает две возможности паттерн-матчинга:
1. Можно делать одновременный матчинг по выражениям, перечисляя их через запятую
2. Можно использовать `_` как паттерн, который матчится с чем угодно.
-/
def sub (x y : Nat) : Nat :=
  match x, y with
  | Nat.succ n, Nat.succ m => sub n m
  | 0, _ => 0
  | _, 0 => x

/-- Задайте сложение натуральных чисел. Нужен ли для этого матчинг по двум аргументам? -/
def add (x y : Nat) : Nat :=
  sorry

/-- Таким "нестандартным" паттерн-матчингом для `Nat` можно задать числа Фибоначчи. -/
def fib (n : Nat) :=
  match n with
  | 0 => 1
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/- Задайте их используя только обычный матчинг с `0` и `n + 1`.

Подсказка: вам может понадобиться вспомогательная функция. -/

def fib' (n : Nat) : Nat :=
  sorry
