import Std.Data.HashSet

namespace hidden

/- ## Задача 1. Контейнеры -/

/-- Класс `Container α β` означает что тип `α` является контейнером для элементов типа `β`.
Напишите необходимые поля для класса сами так чтобы его можно было использовать в фунциях ниже.
Нужно ли где-то добавить `outParam`? -/
class Container (α : Type) (β : Type)

/-- Добавляет элемент в контейнер. -/
def insert {α β : Type} [Container α β] (cont : α) (newElem : β) : α :=
  sorry

/-- Проверяет что в контейнере есть данный элемент. -/
def contains {α β : Type} [Container α β] (cont : α) (elem : β) : Bool :=
  sorry

/-- Добавляет элемент в контейнер только если его там еще нет. -/
def insertIfNew {α β : Type} [Container α β] (cont : α) (newElem : β) : α :=
  sorry

/-- Считает произведение элементов в контейнере. Добавьте недостающие тайпклассы для `β`.

Hint: посмотрите какие классы используются в `List.sum`. -/
def prod {α β : Type} [Container α β] (cont : α) : β :=
  sorry

/-- Считает минимум от элементов в контейнере. Добавьте недостающие тайпклассы для `β`.

Hint: посмотрите какие классы используются в `List.min?`. -/
def min? {α β : Type} [Container α β] (cont : α) : Option β :=
  sorry

/-- Собирает элементы контейнера в список -/
def toList {α β : Type} [Container α β] (cont : α) : List β :=
  sorry

/- Напишите инстансы для `Container` так чтобы примеры ниже заработали -/

def testList : List Nat := [1, 2, 3]
def testMap : Std.HashSet Int := .ofList [24, -24, 0]
def testArray : Array Float := #[3.71, 2.14, 0.99]

#guard contains (insert testList 4) 4
#guard contains (insert testList 42) 42
#guard insertIfNew [1,2,3] 2 == [1,2,3]
#guard toList testArray == [3.71, 2.14, 0.99]
#guard toList (insert testArray 7.7) == [3.71, 2.14, 0.99, 7.7]
#guard contains testMap 24
#guard contains (insert testMap 999) 999
#guard ! (contains testMap 123456)
#guard (insertIfNew testMap 24).toList == testMap.toList
#guard contains (insertIfNew testMap 33) 33
#guard prod testList == 6
#guard min testArray == .some 0.99

/- P.S.: В качестве **бонусных** задач можно сдать `Enumerable BinTree` и `IsPrime` с семинара. -/
