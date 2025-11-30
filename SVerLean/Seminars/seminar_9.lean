import SVerLean.Lectures.lecture_9
import Mathlib.Data.Stream.Init

open SetRel

/- ## Задача 1. Монотонность -/

example {α β : Type} [PartialOrder α] (f g : α → Set β)
    (hf : Monotone f) (hg : Monotone g) :
    Monotone (fun a ↦ f a ∪ g a) := by
  sorry -- докажите по определению

example {α β : Type} [PartialOrder α] (f g : α → SetRel β β)
    (hf : Monotone f) (hg : Monotone g) :
    Monotone (fun a ↦ f a ○ g a) := by
  sorry -- докажите по определению


/- ## Задача 2. Неподвижные точки -/

def F₁ : Set ℤ →o Set ℤ where
  toFun S := {0} ∪ {n + 2 | n ∈ S}
  monotone' := by
    apply Monotone.union
    · apply monotone_const
    · apply Set.monotone_image

/-- Докажите что наименьшая неподвижная точка `F₁` равна множеству натуральных четных чисел. -/
example : F₁.lfp = {n | n % 2 = 0 ∧ n ≥ 0} := by
  sorry

/-- Чему равно `F₁.gfp`? -/
example : F₁.gfp = sorry := by
  sorry

def F₂ : Set (ℕ → ℤ) →o Set (ℕ → ℤ) where
  toFun P := {f | f 0 ≤ f 1} ∩ {f | (fun n ↦ f (n + 1)) ∈ P}
  monotone' := by
    apply Monotone.inter
    · apply monotone_const
    · apply Set.monotone_preimage

/-- Чему равно `F₂.lfp`? -/
example : F₂.lfp = sorry := by
  sorry

/-- Чему равно `F₂.gfp`? -/
example : F₂.gfp = sorry := by
  sorry

/- ## Задача 3. Регулярные выражения

Регулярные выражения, или регекспы (regex), являются популярным инструментом для строковых
задач (например, проверка корректности емейла в форме ввода).
Язык (базовых) регулярных выражений определяется следующей грамматикой:

    R  ::=  ∅
         |  ε
         |  a
         |  R ⬝ R
         |  R + R
         |  R*

Семантика регулярных выражений следующая: каждое регулярное выражение *принимает*
некоторое множество строк (например `^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$`
принимает все корректные емейлы и только их).

* `∅` — не принимает ничего;
* `ε` — принимает пустую строку;
* `a` — принимает атом (символ) `a`;
* `R ⬝ R` — принимает конкатенацию двух регулярных выражений;
* `R + R` — принимает либо одно, либо другое регулярное выражение;
* `R*` — принимает произвольное (возможно нулевое)число повторений регулярного выражения.

Заметьте аналогию с языком WHILE:

    `∅` ~ бесконечный цикл (например, `while true do skip`)
    `ε` ~ `skip`
    `a` ~ `:=`
    `⬝` ~ `;`
    `+` ~ `if then else`
    `*` ~ цикл `while` -/

inductive Regex (α : Type) : Type
  | nothing : Regex α
  | empty   : Regex α
  | atom    : α → Regex α
  | concat  : Regex α → Regex α → Regex α
  | alt     : Regex α → Regex α → Regex α
  | star    : Regex α → Regex α

/-- Постройте теорию аналогичную WHILE и определите денотационную семантику
регулярных выражений. -/
def Regex.denote {α} (r : Regex α) : Set (List α) :=
  match r with
  | Regex.nothing => ∅
  | Regex.empty => {[]}
  | Regex.atom a => {[a]}
  | Regex.concat r1 r2 => {w | ∃ u ∈ r1.denote, ∃ v ∈ r2.denote, w = u ++ v}
  | Regex.alt r1 r2 => r1.denote ∪ r2.denote
  | Regex.star r => sorry

/- ### Абстрактные свойства: -/

example {α} (r : Regex α) : (r.concat .empty).denote = r.denote := by
  sorry

example {α} : (Regex.nothing : Regex α).star.denote = Regex.empty.denote := by
  sorry

example {α} (r : Regex α) :
    r.star.denote = (Regex.alt (.concat r r.star) .empty).denote := by
  sorry

/- ###  Конкретные примеры: -/

/-- Алфавит из трех символов -/
inductive ABC
| a | b | c
deriving BEq

def r1 : Regex ABC := .concat (.atom .a) (.concat (.atom .b) (.atom .c))

example : r1.denote = {[.a, .b, .c]} := by
  sorry

def r2 : Regex ABC := .star (.alt (.atom .a) (.atom .b))

example : [.a, .b] ∈ r2.denote := by
  sorry

/-- Придумайте regex для слов начинающихся на `a`. -/
def r3 : Regex ABC := sorry

example (w) : w ∈ r3.denote ↔ w.headD .b = .a := by
  sorry

/-- Придумайте regex для слов в которых четное количество букв `b`. -/
def r4 : Regex ABC := sorry

example (w) : w ∈ r4.denote ↔ w.count .b % 2 = 0 := by
  sorry
