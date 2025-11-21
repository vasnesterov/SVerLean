import SVerLean.Lectures.lecture_8
open Relation

set_option linter.hashCommand false
set_option linter.style.commandStart false

-- Чтобы `grind` всегда по умолчанию раскрывал `Function.update`
attribute [grind] Function.update

/- # Задача 1. Верификация конкретных программ

Используйте `vcg` и мощные тактики типа `simp`, `grind`, `aesop`.
Почти везде достаточно хорошо аннотировать программу и использовать одну из тактик выше.
-/

/-- **1.1**: Максимум из двух чисел -/
def natMax : Stmt :=
  .ifThenElse (fun s ↦ s "a" < s "b") (
    .assign "result" (fun s ↦ s "b")
  ) (
    .assign "result" (fun s ↦ s "a")
  )

theorem natMax_correct (x y : ℕ) :
    {fun s ↦ s "a" = x ∧ s "b" = y }natMax{ fun s ↦ s "result" ≥ x ∧ s "result" ≥ y } := by
  sorry

/-- **1.2**: Бесконечный цикл -/
def infiniteLoop : Stmt :=
  .whileDo (fun _ ↦ True) .skip

theorem infiniteLoop_correct :
    {fun _ ↦ True}infiniteLoop{ fun _ ↦ False } := by
  sorry

/-- **1.3**: Счетчик до 10 -/
def counter : Stmt :=
  .whileDo (fun s ↦ s "i" < 10) (
    .assign "i" (fun s ↦ s "i" + 1)
  )

theorem counter_correct :
    {fun s ↦ s "i" < 10}counter{ fun s ↦ s "i" = 10 } := by
  sorry

/-- В `counter_correct` можно убрать предусловие.
Можно ли придумать инвариант для этого случая? -/
theorem counter_correct' :
    {fun _ ↦ True}counter{ fun s ↦ s "i" = 10 } := by
  sorry

/-- **1.4**: Вычисляет `m ^ n`. -/
def slowPow : Stmt :=
  .assign "result" 1;
  .assign "i" 0;
  .whileDo (fun s ↦ s "i" < s "n") (
    .assign "result" (fun s ↦ s "result" * s "m");
    .assign "i" (fun s ↦ s "i" + 1)
  )
-- P.S.: fastPow - в домашке

theorem slowPow_correct (m n : ℕ) :
    {fun s ↦ s "m" = m ∧ s "n" = n }slowPow{ fun s ↦ s "result" = m ^ n } := by
  sorry

/-- **1.5**: алгоритм Евклида для вычисления наибольшего общего делителя -/
def gcd : Stmt :=
  .whileDo (fun s ↦ s "b" > 0) (
    .assign "a" (fun s ↦ s "a" % s "b");
    -- swap a and b:
    .assign "t" (fun s ↦ s "a");
    .assign "a" (fun s ↦ s "b");
    .assign "b" (fun s ↦ s "t")
  )

theorem gcd_correct (x y : ℕ) :
    { fun s ↦ s "a" = x ∧ s "b" = y }gcd{ fun s ↦ s "a" = Nat.gcd x y } := by
  sorry


/- # Задача 2. Логические свойства троек Хоара -/

/-
**3.1**
Верно ли следующее утверждение:
Для любой программы `S` можно найти "наилучшие" предусловие и постусловие,
т.е. существуют `P` и `Q` такие что `{P}S{Q}` и для любого `P'` и `Q'` таких что `{P'}S{Q'}`
выполняется `P → P'` и `Q' → Q`. Иными любую верную тройку `{P'}S{Q'}` можно вывести из `{P}S{Q}`
при помощи правила `consequence`.
-/

def existsBestTriple (S : Stmt) : Prop :=
  ∃ P Q, {P}S{Q} ∧ ∀ P' Q', {P'}S{Q'} →
    (∀ s, P s → P' s) ∧ (∀ t, Q' t → Q t)

-- Если да, докажите
example (S : Stmt) : existsBestTriple S := by
  sorry

-- Если нет, приведите контрпример.

def counterExample : Stmt := sorry

example : ¬ existsBestTriple counterExample := by
  sorry

/--
**3.2**
Докажите что для данной программы и предусловия, существует самое сильное постусловие.
То есть такое которое влечет все остальные. -/
example (S : Stmt) (P : State → Prop) : ∃ Q, {P}S{Q} ∧ ∀ Q', {P}S{Q'} → ∀ t, Q t → Q' t := by
  sorry
-- P.S.: верно и симметричное утверждение: для любой программы и постусловия,
-- существует самое слабое предусловие.

/-
**3.3**
Верно ли утверждение:
Пусть дано постусловие `Q`. Если `P` и `P'` не равны, то существует программа `S` такая что
`{P}S{Q}`, но не`{P'}S{Q}`. Если да, докажите. Если нет, приведите контрпример.
-/

/--
**3.4**
Верно ли это утверждение? Докажите или приведите контрпример.
Если верно, выводимо ли оно по правилам вывода для троек Хоара? -/
example (P₁ P₂ Q₁ Q₂ S) (h₁ : {P₁}S{Q₁}) (h₂ : {P₂}S{Q₂}) :
    {fun s ↦ P₁ s ∨ P₂ s}S{fun s ↦ Q₁ s ∨ Q₂ s} := by
  sorry

-- Верно ли это утверждение? Докажите или приведите контрпример.
example (P₁ P₂ Q₁ Q₂ S) (h : {fun s ↦ P₁ s ∨ P₂ s}S{fun s ↦ Q₁ s ∨ Q₂ s}) :
    {P₁}S{Q₁} ∨ {P₂}S{Q₂} := by
  sorry
