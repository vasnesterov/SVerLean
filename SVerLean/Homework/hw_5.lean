import Mathlib

/- # Задача 1. Кванторы -/

example (f : ℕ → ℕ) (hf : ∀ x y, f (x + y) = f x - f y) : ∀ x, f x = 0 := by
  sorry

example {α : Type} (P : α → Prop) : (¬ ∀ x, P x) → ∃ x, ¬ P x := by
  sorry

/--
Математический смысл: пусть `f : ℕ → ℕ`, которая
1. В нуле равна нулю
2. Монотонна
3. Но растет медленно: ∀ n, f (n + 1) ≤ f n + 1
4. Неограничена: т.е. для любого `C` существует `x` т.ч. `f x ≥ C`

Тогда она принимает все возможные значения.
-/
example (f : ℕ → ℕ) (hf₀ : f 0 = 0) (hf₁ : ∀ n, f n ≤ f (n + 1)) (hf₂ : ∀ n, f (n + 1) ≤ f n + 1)
    (h : ∀ C, ∃ x, f x ≥ C) : ∀ C, ∃ x, f x = C := by
  sorry

/- # Задача 2. Индукция: NAND-формулы

Возьмем процедуру перевода логической формулы в NAND-формулу (см. дз №2)
Докажем что она корректна в том смысле что NAND-перевод формулы вычисляется так же
как и исходная формула.
-/

inductive BooleanFormula : Type
| bool : Bool → BooleanFormula
| var  : String → BooleanFormula
| not  : BooleanFormula → BooleanFormula
| and  : BooleanFormula → BooleanFormula → BooleanFormula
| or   : BooleanFormula → BooleanFormula → BooleanFormula
deriving BEq

def BooleanFormula.eval (f : BooleanFormula) (env : String → Bool) : Bool :=
  match f with
  | bool b   => b
  | var  s   => env s
  | not  b   => !(b.eval env)
  | and  a b => (a.eval env) && (b.eval env)
  | or   a b => (a.eval env) || (b.eval env)

inductive NandFormula : Type
| bool : Bool → NandFormula
| var  : String → NandFormula
| nand : NandFormula → NandFormula → NandFormula
deriving BEq

def NandFormula.eval (f : NandFormula) (env : String → Bool) : Bool :=
  match f with
  | bool b   => b
  | var  s   => env s
  | nand a b => !((a.eval env) && (b.eval env))

def BooleanFormula.toNandFormula (f : BooleanFormula) : NandFormula :=
  match f with
  | bool b   => .bool b
  | var  s   => .var s
  | not  b   => .nand b.toNandFormula (.bool true)
  | and  a b => .nand (.nand a.toNandFormula b.toNandFormula) (.bool true)
  | or   a b =>
    .nand (.nand a.toNandFormula a.toNandFormula) (.nand b.toNandFormula b.toNandFormula)

theorem BooleanFormula.toNandFormula_eval (f : BooleanFormula) (env : String → Bool) :
    f.toNandFormula.eval env = f.eval env := by
  sorry

/- # Задача 3. Верификация: бинарный поиск -/

/-- Проверяет есть ли в векторе `vec` элемент `x`. В этой функции мы
*предполагаем* что список отсортирован, но не добавляем это как
Prop-аргумент функции. Это общая философия Lean/Mathlib: если
для функции Prop-аргументы не требуются, их туда и не добавляют.
Зато их добавляют в теоремы (как ниже). То есть функцию можно запустить
на "некорректном" входе, но для доказательств мы накладываем
требование корректности на вход. -/
def Vector.sortedContains {n : Nat} (vec : Vector Int n) (x : Int) : Bool :=
  match n with
  | 0 => false
  | m + 1 => go vec 0 ⟨m, by grind⟩
where
  go {m : Nat} (vec : Vector Int (m + 1)) (left right : Fin (m + 1)) : Bool :=
    if right.val - left.val ≤ 1 then
      if left == x then
        true
      else
        false
    else
      let middle : Fin (m + 1) := ⟨(left.val + right.val) / 2, by grind⟩
      if vec[middle] ≤ x then
        go vec middle right
      else
        go vec left middle
  termination_by right.val - left.val
  decreasing_by all_goals grind

/-- Если вектор, то в нем есть элемент `x` тогда и только тогда, когда
наша функция возвращает `true`. -/
theorem Vector.sortedContains_correct {n : Nat} {vec : Vector Int n} {x : Int}
    (h : ∀ i j : Fin n, i < j → vec[i] ≤ vec[j]) -- вектор отсортирован
    :
    (∃ i : Fin n, vec[i] = x) ↔
    Vector.sortedContains vec x = true := by
  sorry

/- ## Бонус 1: Вычисление квадратного корня методом Герона

Пусть дано положительное рациональное число `x`.
Как посчитать его квадратный корень с хорошей точностью?

В этой задаче предлагается заполнить `sorry` и получить верифицированный
быстрый алгоритм для вычисления квадратного корня.
-/

/--
Алгоритм следующий:
мы итеративно вычисляем последовательность приближений:
`y₀ = x + 1`
`yₙ₊₁ = (yₙ + x / yₙ) / 2`
которые все ближе сходятся к корню.
-/
def approximateSqrt (x : ℚ) (nSteps : ℕ) : ℚ :=
  go (x + 1) nSteps
where
  go (y : ℚ) (nSteps : ℕ) : ℚ :=
    match nSteps with
    | 0 => y
    | nSteps + 1 =>
      let y' := (y + x / y) / 2
      go y' nSteps

#eval (approximateSqrt 2 4).toFloat

/-- Относительная погрешность приближения.
Измеряет насколько близок `y²` к `x` (и, значит, `y` к `√x`). -/
def err (x y : ℚ) : ℚ :=
  y ^ 2 / x - 1

/-- Формула для ошибки на следующем шаге -/
theorem err_step_eq {x y : ℚ} (hx_pos : 0 < x) (hy_pos : 0 < y) :
    err x ((y + x / y) / 2) = 4⁻¹ * (err x y) ^ 2 / (1 + err x y) := by
  sorry

/-- После любого шага ошибка неотрицательна -/
theorem err_step_nonneg {x y : ℚ} (hx_pos : 0 < x) (hy_pos : 0 < y) :
    0 ≤ err x ((y + x / y) / 2) := by
  sorry

/-- Оценка сверху на ошибку. Используйте `err_step_eq`. -/
theorem err_step_le {x y : ℚ} (hx_pos : 0 < x) (hy_pos : 0 < y)
    (h_err_nonneg : 0 ≤ err x y) :
    err x ((y + x / y) / 2) ≤ err x y * 4⁻¹ := by
  sorry

/-- Ошибка после применения `go` `n` раз. По сути это `n` раз примененная
`err_step_le`. Используйте индукцию. -/
theorem approximateSqrt_go_err {x y : ℚ} {n : ℕ} (hx_pos : 0 < x) (hy_pos : 0 < y)
    (h_err_nonneg : 0 ≤ err x y) :
    err x (approximateSqrt.go x y n) ≤ (err x y) * (4⁻¹) ^ n := by
  sorry

/-- Итоговая теорема, показывающая что ошибка `approximateSqrt x n` убывает
экспоненционально. -/
theorem approximateSqrt_err {x : ℚ} {n : ℕ} (hx_pos : 0 < x) :
    err x (approximateSqrt x n) ≤ (x + 1) ^ 2 / x * (4⁻¹) ^ n := by
  sorry

/-- Числовой пример: для вычисления корня из 2 с точностью `4e-6` достаточно
10 шагов.

P.S.: на самом деле метод сходится гораздо быстрее: если стартовать рядом с корнем,
то число верных цифр на каджом шаге удваивается. А мы доказали что каждый шаг дает
нам O(1) новых верных цифр. -/
example : err 2 (approximateSqrt 2 10) ≤ (9 / 2) * (4⁻¹) ^ 10 := by
  convert approximateSqrt_err _
  all_goals norm_num

#eval ((9 / 2) * (4⁻¹ : ℚ) ^ 10).toFloat



/- **Бонус 2**: докажите что `bestResponse s` со второго семинара действительно
всегда выигрывает всухую против `s`. -/
