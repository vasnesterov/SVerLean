import SVerLean.Lectures.lecture_8
open Relation

set_option linter.hashCommand false
set_option linter.style.commandStart false

-- Чтобы `grind` всегда по умолчанию раскрывал `Function.update`
attribute [grind] Function.update

/- # Задача 1. Верификация конкретных программ

Верифицируйте следующие программы. Пользуйтесь `vcg` и мощными тактиками: `simp`, `grind`, `aesop`.
-/

/-- Быстрое возведение в степень `m ^ n` за `O(log n)`. -/
def fastPow : Stmt :=
  .assign "result" 1;
  .whileDo (fun s ↦ s "n" > 0) (
    .ifThenElse (fun s ↦ s "n" % 2 != 0) (
      .assign "result" (fun s ↦ s "result" * s "m")
    ) (
      .skip
    );
    .assign "n" (fun s ↦ s "n" / 2);
    .assign "m" (fun s ↦ s "m" * s "m")
  )


-- Подсказка: возможно понадобятся леммы типа `Nat.div_mul_self_eq_mod_sub_self`
-- Ищите их в Loogle
theorem fastPow_correct (m n : ℕ) :
    {fun s ↦ s "m" = m ∧ s "n" = n }fastPow{ fun s ↦ s "result" = m ^ n } := by
  sorry

/-- Числа Фибоначчи: `0, 1, 1, 2, 3, ...` -/
def fib : Stmt :=
  .assign "a" (fun _ ↦ 0);
  .assign "b" (fun _ ↦ 1);
  .assign "i" (fun _ ↦ 0);
  .whileDo (fun s ↦ s "i" < s "n") (
    .assign "t" (fun s ↦ s "a");
    .assign "a" (fun s ↦ s "b");
    .assign "b" (fun s ↦ s "t" + s "b");
    .assign "i" (fun s ↦ s "i" + 1)
  )

theorem fib_correct (n : ℕ) :
    {fun s ↦ s "n" = n }fib{ fun s ↦ s "a" = Nat.fib n } := by
  sorry

/- # Задача 2. Тотальная логика Хоара -/

-- Докажите основное правило для тотальной логики Хоара: правило для `while`.
example {B P S} (v : State → ℕ)
    (hS : ∀ v₀, [* fun s ↦ P s ∧ B s ∧ v s = v₀ *]S[* fun s ↦ P s ∧ v s < v₀ *]) :
    [* P *](.whileDo B S)[* fun s ↦ P s ∧ ¬ B s *] := by
  sorry

-- Вопрос: для любого ли корректного цикла можно подобрать подходящую функцию `v`?
-- (ответьте текстом здесь)

/- Докажите тотальную корректность для примеров из предыдущей задачи. -/

theorem fastPow_total_correct (m n : ℕ) :
    [* fun s ↦ s "m" = m ∧ s "n" = n *]fastPow[* fun s ↦ s "result" = m ^ n *] := by
  sorry

theorem fib_total_correct (n : ℕ) :
    [* fun s ↦ s "n" = n *]fib[* fun s ↦ s "a" = Nat.fib n *] := by
  sorry

-- Вопрос: правда ли что для любых условий `P` и `Q` существует программа `S` такая что
-- `[* P *]S[* Q *]`?
-- (ответьте текстом здесь)
