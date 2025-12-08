import Mathlib
import Std

open Std.Do

set_option mvcgen.warning false

/- # Задача 1. Монадичность Nondet -/

namespace Problem1

/-- `Nondet α` означает недетерминированное вычисление типа `α`. -/
inductive Nondet (α : Type) : Type
  /-- Детерминированное вычисление в `α`. -/
  | just   : α → Nondet α
  /-- Неудачное вычисление. -/
  | fail   : Nondet α
  /-- Ветвление: `f : Bool → Nondet α` выдает вычисление для каждой ветви.
  В данном случае их две: `f true` и `f false`. Но можно заменить `Bool` на другой тип. -/
  | choice : (Bool → Nondet α) → Nondet α

/- Докажите что `Nondet` является монадой. После этого легко будет сделать бонусы
в предыдущей домашке. -/

instance : Monad Nondet := sorry

instance : LawfulMonad Nondet := sorry

end Problem1

/- # Задача 2. Куча

Реализуйте кучу на основе массива при помощи монады `StateM`.
Используйте https://ru.algorithmica.org/cs/basic-structures/heap/ как референс.
Заменяйте `while` на рекурсию (`mvcgen` не умеет рассуждать про `while`, потому что `while`
это `partial` функция).

(Задача сложная)
-/

namespace Problem2

structure Heap where
  heap : Array Nat
deriving Repr

abbrev HeapM := StateM Heap

def siftUp (v : Nat) : HeapM Unit := do
  sorry

/-- `bound` понадобится чтобы доказать завершение рекурсии. -/
def siftDownImp (v : Nat) (bound : Nat) : HeapM Unit := do
  sorry

def siftDown (v : Nat) : HeapM Unit := do
  siftDownImp v (← get).heap.size

/- `getMin`, `insert` и `removeMin` реализуются через `siftUp` и `siftDown`.
Можете поменять их если нужно. -/

-- `WithTop Nat` это синоним для `Option Nat` где `none` интерпретируется как `∞` которая больше
-- любого натурального числа. Она возвращается если куча пуста.
def getMin : HeapM (WithTop Nat) := do pure (← get).heap[1]?

def insert (x : Nat) : HeapM Unit := do
  modify (fun ⟨heap⟩ => ⟨heap.push x⟩)
  siftUp ((← get).heap.size - 1)

def removeMin : HeapM Unit := do
  modify (fun ⟨heap⟩ => ⟨(heap.set! 1 heap.back!).pop⟩)
  siftDown 0

instance : ToString (WithTop Nat) where
  toString x := match x with
  | .some x => toString x
  | .none => "∞"

def test : HeapM <| Array (WithTop Nat) := do
  let mut res := #[]
  res := res.push (← getMin)
  insert 2
  res := res.push (← getMin)
  insert 3
  res := res.push (← getMin)
  insert 1
  res := res.push (← getMin)
  removeMin
  res := res.push (← getMin)
  removeMin
  res := res.push (← getMin)
  insert 2
  res := res.push (← getMin)
  insert 5
  res := res.push (← getMin)
  insert 0
  res := res.push (← getMin)
  dbg_trace (← getMin)
  return res

#guard (test.run' ⟨#[0]⟩).run == #[⊤, 2, 2, 1, 2, 3, 2, 2, 0]

/-- Интерпретация кучи как мультимножества (по сути денотационная семантика). -/
def Heap.toMultiset (h : Heap) : Multiset Nat :=
  .ofList h.heap.toList

/- Докажите корректность операций `getMin`, `insert` и `removeMin` относительно этой семантики
при помощи `mvcgen`. -/

/-- Например для `getMin` условие корректности будет таким: -/
theorem getMin_correct (h : Heap) :
    ⦃fun s => ⌜s = h⌝ ⦄getMin⦃⇓r => ⌜(h.toMultiset.map (fun x => .some x)).inf = r⌝⦄ := by
  sorry

end Problem2

/- **Бонус**: "декоратор" для сохранения предыдущих вычислений.

В Python есть декоратор `functools.lru_cache` для сохранения предыдущих вычислений.
Если навесить его на функцию, то при вызове функции с аргументами, которые уже были вычислены,
будет возвращаться результат из кэша, а не вычисляться заново.

Примерно так это будет выглядеть в Lean:
-/

abbrev CacheM (α β : Type) [BEq α] [Hashable α] := StateM (Std.HashMap α β)

/-- Оригинальная функция для референса -/
def fib (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 1
  | m + 2 => fib m + fib (m + 1)

/- Декорированная `fib`. Вопрос: как реализовать такой декоратор в общем виде? Нужно ли подниматься
на метауровень? -/
mutual
  def fibMBody (n : ℕ) : CacheM ℕ ℕ ℕ := do
    match n with
    | 0 => pure 0
    | 1 => pure 1
    | m + 2 => pure <| (← fibM m) + (← fibM (m + 1))

  def fibM (n : ℕ) : CacheM ℕ ℕ ℕ := do
    match (← get).get? n with
    | some val => pure val
    | none =>
      let res ← fibMBody n
      modify (fun s => s.insert n res)
      pure res
end

/-- Докажите корректность `fibM` при помощи `mvcgen`. -/
theorem fibM_correct (n : ℕ) :
    (fibM n).run' ∅ = fib n := by
  sorry


/- **Бонус**: на курсе мы неоднократно вычисляли числа Фибоначчи за O(N) вместо O(2ⁿ) и
степень `m ^ n` за O(log n) вместо O(n). Числа Фибоначчи тоже можно вычислять за O(log n):

Обозначим v(n) = (fib n, fib (n + 1)) -- вектор ℕ². Тогда v(n + 1) = M * v(n), где
M = |0 1|
    |1 1|

Стало быть, v(n) = Mⁿ * v(0) = Mⁿ * (0, 1).
(В целом такой подход работает для любой линейной динамики)

Используя бинарное возведение в степень для матриц, можно вычислить Mⁿ за O(log n), и тем
самым получить число Фибоначчи. Реализуйте этот алгоритм и докажите его корректность.
-/
