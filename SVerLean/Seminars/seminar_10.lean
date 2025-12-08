import Mathlib
import Std

open Std.Do

set_option mvcgen.warning false

/- # Задача 1. Снова Фибоначчи -/

namespace Problem1

def fib (n : ℕ) : ℕ := match n with
  | 0 => 0
  | 1 => 1
  | m + 2 => fib m + fib (m + 1)

/-- Напишите императивную реализацию `fib` при помощи монады `Id` и двух
мутабельных переменных. -/
def fibId (n : ℕ) : ℕ := Id.run do
  sorry

/-- Докажите корректность `fibId` при помощи `mvcgen`. -/
theorem fibId_correct (n : ℕ) : fibId n = fib n := by
  sorry

end Problem1

/- # Задача 2. Снова скобочные последовательности -/

namespace Problem2

inductive Bracket
| op
| cl

instance : ToString Bracket where
  toString b := match b with
  | .op => "("
  | .cl => ")"

inductive CorrectBS : (List Bracket) → Prop
| empty : CorrectBS []
| append {left right : List Bracket}
  (h_left : CorrectBS left) (h_right : CorrectBS right) : CorrectBS (left ++ right)
| enclose {bs : List Bracket} (h : CorrectBS bs) : CorrectBS (.op :: bs ++ [.cl])

/-- Напишите функцию проверки правильности скобочной последовательности при помощи монады `Id` -/
def check (seq : List Bracket) : Bool := Id.run do
  sorry

#guard check []
#guard ! check [.op]
#guard check [.op, .cl]
#guard ! check [.cl]
#guard ! check [.op, .cl, .cl, .op]
#guard check [.op, .cl, .op, .cl]
#guard check [.op, .op, .cl, .cl]

/-- Докажите корректность `check` при помощи `mvcgen`.
Добавьте леммы с аттрибутом `grind` до этой теоремы, так чтобы её доказательство не содержало
нетривиальных рассуждений. -/
theorem check_correct (seq) (h : CorrectBS seq) :
    check seq = true := by
  sorry

end Problem2

/- # Задача 3. Поиск коллизий в хеш-функциях

Допустим дана хеш-функция `hash : ℕ → α` и мы хотим найти два различных числа
`x` и `y` такие что `hash x = hash y`. Если для хэш-функции это сделать легко, то в криптографии
её использовать нельзя.

Из "парадокса дней рождения" вытекает что если мы возьмем случайные `O(√|α|)` чисел, то с высокой
вероятностью найдем коллизию среди каких-то двух из них и от самой функции `hash` это никак не
зависит. В этой задаче предлагается реализовать этот метод используя `RandT`.
-/

namespace Problem3

variable {α : Type} [BEq α] [Hashable α]

/-- Генерирует случайное натуральное число. -/
def randNat : RandT (Except String) ℕ :=
  Rand.next

/-- Напишите функцию которая находит два различных числа `x` и `y` такие что `hash x = hash y`.
В случае неудачи бросайте исключение. -/
def findCollision (hash : ℕ → α) : RandT (Except String) (ℕ × ℕ) := do
  sorry

def test (hash : ℕ → α) : IO Bool := do
  let .ok (x, y) := (findCollision hash).run' (ULift.up <| mkStdGen 42) | return false
  dbg_trace (x, y)
  return hash x == hash y

/-- Некоторая хеш-функция -/
def murmur3 (x₀ : ℕ) := Id.run do
  let mut x := x₀
  x := x ^^^ (x >>> 16)
  x := x * 0x7feb352d
  x := x ^^^ (x >>> 15)
  x := x * 0x846ca68b
  x := x ^^^ (x >>> 16)
  pure x.toUInt32

-- проверьте что тут `true`
#eval test (fun x ↦ (hash x).toUInt8)
#eval test (murmur3)

/-- Докажите корректность `findCollision` при помощи `mvcgen`.
Добавьте спецификацию для `randNat` до этой теоремы, так чтобы её доказательство не содержало
нетривиальных рассуждений. -/
theorem findCollision_correct [LawfulBEq α] (hash : ℕ → α) :
    ⦃⌜True⌝⦄findCollision hash⦃⇓? (x, y) => ⌜x ≠ y ∧ hash x = hash y⌝⦄ := by
  sorry

end Problem3

/- # Задача 4.

Одна из знаменитых NP-трудных задач -- это задача о коммивояжере: есть `n` городов и
расстояния между ними. Нужно объехать все города, посетив каждый из них ровно один раз,
минимизировав пройденное расстояние.

Одна из возможных эвристик для решения этой задачи: возьмем случайный порядок объезда городов
и будем пытаться улучшать его. Для этого будем брать два случайных города и пытаться их поменять
местами, если это уменьшает длину пути.

Известно, что если метрика расстояний между городами евклидова, то такая эвристика находит
решение длины не более чем в Θ(log n / log log n) раз хуже оптимального.
-/

namespace Problem4

structure Path (α : Type) where
  points : Array α
  /-- Мы будем отдельно хранить длину пути, чтобы быстро обновлять её. -/
  length : ℝ

abbrev PathM (α : Type) := StateM (Path α)

-- абстрагируемся от городов и будем жить в произвольном метрическом пространстве
variable {α : Type} [MetricSpace α]

/-- "Честная" длина пути -- сумма расстояний между соседними городами. -/
def pathLength (path : List α) : ℝ :=
  (path.zip path.tail).map (fun (x, y) => dist x y) |>.sum

/-- Добавляет город в конец пути. -/
def pushPoint (p : α) : PathM α Unit := do
  sorry

/-- Докажите корректность `pushPoint` при помощи `mvcgen`. -/
theorem pushPoint_correct (p : α) :
    ⦃fun s => ⌜pathLength s.points.toList = s.length⌝⦄pushPoint (α := α) p⦃⇓ _ s => ⌜pathLength s.points.toList = s.length⌝⦄ := by
  sorry

/-- Меняет местами `i`-ый и `i + 1`-ый города, если это уменьшает длину пути. -/
noncomputable def swapPointsIfShorter (i : ℕ) : PathM α Unit := do
  modify (fun s =>
    if h : i + 1 < s.points.size then
      let a := if h : i > 0 then dist s.points[i - 1] s.points[i] else 0
      let b := if h : i + 2 < s.points.size then dist s.points[i + 1] s.points[i + 2] else 0
      let c := if h : i > 0 then dist s.points[i - 1] s.points[i + 1] else 0
      let d := if h : i + 2 < s.points.size then dist s.points[i] s.points[i + 2] else 0
      if a + b > c + d then
        ⟨s.points.swap i (i + 1), s.length - a - b + c + d⟩
      else
        s
    else
      s
  )

/-- Оптимизирует путь при помощи эвристики. (Предполагается запускать эту функцию несколько раз
до сходимости) -/
noncomputable def optimizePath : PathM α Unit := do
  for i in [:(← get).points.size - 1] do
    swapPointsIfShorter i

/- Докажите 2 теоремы о корректности `optimizePath` при помощи `mvcgen`: -/

theorem optimizePath_correct_1 (len : ℝ) :
    ⦃fun s => ⌜s.length = len⌝⦄optimizePath (α := α)⦃⇓ _ s => ⌜s.length ≤ len⌝⦄ := by
  sorry

theorem optimizePath_correct_2 :
    ⦃fun s => ⌜pathLength s.points.toList = s.length⌝⦄optimizePath (α := α)⦃⇓ _ s => ⌜pathLength s.points.toList = s.length⌝⦄ := by
  sorry

end Problem4
