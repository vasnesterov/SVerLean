import Mathlib

/- ## Кванторы: ∀ и ∃ -/

example : ∀ n : ℕ, n + 20 > 8 := by
  -- раньше `intro` вводило в контекст факты (например `hP : P`)
  -- так же можно вводить объекты (как `n : ℕ`)
  -- на уровне теории типов это работает одинаково
  intro n
  -- `grind` это умная тактика которая доказывает
  -- "очевидные" цели в некоторых областях, в частности
  -- про натуральные/целые числа и
  -- пропозициональную логику
  omega

-- квантор `∀` - это просто (зависимая) стрелка
example : (n : ℕ) → n + 20 > 8 := by
  intro n
  grind

-- но более конвенционально писать так:
example (n : ℕ) : n + 20 > 8 := by
  grind







-- как использовать гипотезу с `∀`?

example (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 4) : f 20 ≤ 4 := by
  -- это работает, ведь `∀` это просто стрелка
  -- change (n : ℕ) → f n ≤ 4 at hf
  apply hf

example (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 4) : f 20 ≤ 4 := by
  -- `exact` тоже работает, но `n` нужно указать явно
  -- `apply` его вывел сам из типа цели
  exact hf 20

example (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 4) : f 20 < 7 := by
  -- `specialize` "подставляет" конкретное выражение
  -- в квантор
  specialize hf 20
  -- дальше `grind` разберется
  grind

example (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 4) : f 20 + f 30 < 9 := by
  -- можно и через `have` (или `suffices`)
  have h1 : f 20 ≤ 4 := hf 20
  have h2 : f 30 ≤ 4 := by
    apply hf
  -- дальше `grind` разберется
  grind










-- как доказать что что-то существует?

example : ∃ x : ℕ, x^2 + x - 1 = 11 := by
  -- `use` позволяет доказать что существует `x`,
  -- обладающий некоторым свойством, предъявив
  -- такой `x`, и затем доказав что он обладает свойством
  use 3
  -- `norm_num` вычисляет все числовые подвыражения
  -- (без переменных)
  norm_num

example (n : ℕ) : ∃ m, m > n := by
  use n + 1
  grind

-- как использовать гипотезу с `∃`?

example (n : ℕ) (h : ∃ m, m < n) : n ≠ 0 := by
  -- гипотезы с квантором существования можно
  -- распаковывать как гипотезы с конъюнкцией
  obtain ⟨m, hm⟩ := h
  -- получили в контекст `m : ℕ` и `hm : m < n`
  -- теперь этот `m` можно использовать
  grind







/- ## Переписывание -/

example (x y z : List String) (hx : x = y ++ z) (hz : z.length > 5) :
    x.length > 5 := by
  -- если `hx : A = B` то `rw [hx]` заменяет все `A`
  -- в цели на `B`
  rw [hx]
  -- логично предположить что в библиотеке есть лемма
  -- (y ++ z).length = y.length + z.length
  rw [List.length_append]
  -- дальше уже `grind` справится
  grind

example (x y z : List String) (hx : x = y ++ z) (hz : z.length > 5) :
    x.length > 5 := by
  --  можно писать в одну строчку
  rw [hx, List.length_append]
  grind

-- `rw` можно использовать с леммами с доп. условиями
-- (говоря формально `h` может иметь тип `P₁ → P₂ → ... → A = B`,
-- и тогда `Pᵢ` станут новыми целями)
example (li : List Int) (h : li.tail.length = 5) : li.length = 6 := by
  -- знак `←` означает "переписывай справа налево", т.е.
  -- заменяй `B` на `A`
  rw [← List.length_tail_add_one]
  -- после этого 2 цели: одна - переписанная старая,
  -- вторая -- доп. условие леммы (непустота листа)
  · grind
  · grind

-- переписывать можно не только с помощью равенств,
-- но и с помощью эквивалентностей (`↔`)
-- (P.S.: но больше ни с чем, только `=` и `↔`)
example (P Q R S : Prop) (hPR : P ↔ R) (hQS : Q ↔ S) (h : P ∧ ¬ Q) : R ∧ ¬ S := by
  -- `at` позволяет переписать в гипотезе
  rw [hPR, hQS] at h
  exact h

/-
`simp` работает как `rw`, но кроме переданных ему лемм (которых вообще может не быть) он использует леммы
вида `A = B` или `A ↔ B` из библиотеки помеченные аттрибутом `@[simp]`. Если какое-то подвыражение текущей цели
совпадает с левой частью в лемме, то она заменяется на правую часть. Цель тактики `simp` -- привести
выражение к "нормальной форме" насколько это возможно. Например есть `simp`-леммы
в которых доказано `|1| = 1`, `p ∧ True ↔ p`, `List.length List.nil = 0`, `x ∈ {y | P y} ↔ P x` и т.п.
Применяя `simp` к выражениям содержащим левые части этих лемм, мы упрощаем эти выражения и с ними становится
легче работать.

Подробнее можно прочитать в секциях Rewriting и Using the Simplifier здесь:
https://leanprover.github.io/theorem_proving_in_lean4/tactics.html
-/

example (x y z : List String) (hx : x = y ++ z) (hz : z.length > 5) :
    x.length > 5 := by
  simp [hx]
  -- `simp` сам применил `List.length_append`
  grind

example (n : ℕ) : List.range 0 ++ ([] ++ [(n + 1) * 0]).reverse = [n - n] := by
  simp

example (n : ℕ) : n + 1 = 1 + n := by
  grind




















/- ## Индукция -/

example (n : ℕ) : n = 0 ∨ ∃ m, n = m + 1 := by
  -- тактика `cases` синтаксически похожа на `match`
  -- (но с меньшим количеством сахара)
  -- и позволяет делать разбор случаев "поконструкторно".
  -- Работает для любого индуктивного типа (или предиката)
  cases n with
  | zero =>
    -- здесь `n` заменилось на `0` во всем контексте
    left
    rfl
  | succ m =>
    -- здесь `n` заменилось на `m + 1` во всем контексте
    right
    use m

example (n : ℕ) : n = 0 ∨ ∃ m, n = m + 1 := by
  -- компактный вариант через `obtain`
  obtain _ | m := n
  · left
    rfl
  · right
    use m

def mySum (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | m + 1 => mySum m + (m + 1)

#eval mySum 3

example (n : ℕ) : 2 * mySum n = n * (n + 1) := by
  -- `induction` позволяет рассуждать по индукции
  -- синтаксически похожа на `cases` но в каждом "рекурсивном"
  -- случае в контексте появляются индуктивные гипотезы
  induction n with
  | zero =>
    -- база индукции
    simp [mySum]
  | succ m ih =>
    -- `ih` доказывает что цель верна для `m`
    -- а нам нужно доказать для `n = m + 1`
    -- то есть совершить индуктивный шаг
    simp [mySum]
    rw [mul_add, ih]
    grind

-- вместо `induction` можно использовать рекурсию, как
-- в функциях - сослаться на доказываемую теорему.
-- Lean проверит что рекурсия корректная и примет
-- доказательство
theorem mySum_eq (n : ℕ) : 2 * mySum n = n * (n + 1) := by
  cases n with
  | zero =>
    simp [mySum]
  | succ m =>
    simp [mySum]
    rw [mul_add, mySum_eq m]
    grind

-- все работает аналогично с другими индуктивными типами

def List.myMap {α β : Type} (f : α → β) (li : List α) : List β :=
  match li with
  | [] => []
  | hd :: tl => f hd :: List.myMap f tl

def List.myLength {α : Type} (li : List α) : Nat :=
  match li with
  | [] => 0
  | hd :: tl => List.myLength tl + 1

example {α β : Type} (f : α → β) (li : List α) :
    (li.myMap f).myLength = li.myLength := by
  induction li with
  | nil =>
    rfl
  | cons hd tl ih =>
    simp [List.myMap, List.myLength]
    exact ih













/- # Decidable -/

-- любой Bool конвертирутся в Prop:
-- true ↦ True, false ↦ False
#synth CoeTC Bool Prop


-- обратная операция: по Prop-у понять верен он или нет -
-- неразрешимая задача. Но в конкретных ситуациях она
-- может быть разрешимой

#check Decidable

def max (a b : Nat) : Nat :=
  if ∃ n, n ≤ a ∧ a ^ n + b ^ n = 20 then
    b
  else
    a

instance (n m : Nat) : Decidable (n < m) := by sorry

/- Сравнение натуральных чисел разрешимо -/
example (n m : Nat) : Decidable (n < m) := by
  infer_instance

/- Если `P` и `Q` разрешимые, то и логические выражения от них разрешимы -/
example (P Q : Prop) [Decidable P] [Decidable Q] :
    Decidable (P ∧ Q) := by
  infer_instance

/- Проверка что существует `m ≤ n` удовлетворяющий разрешимому свойству
`P` тоже разрешима (потому что это конечный перебор). -/
example (n : Nat) (P : Nat → Prop) [∀ m, Decidable (P m)] :
    Decidable (∃ m, m ≤ n ∧ P m) := by
  infer_instance

#check Decidable

instance decideLE (n m : Nat) : Decidable (n ≤ m) :=
  match n with
  | 0 => .isTrue (by exact Nat.zero_le m)
  | k + 1 =>
    match m with
    | 0 => .isFalse (by simp)
    | l + 1 =>
      match decideLE k l with
      | .isTrue proof =>
        .isTrue (by exact Nat.add_le_add_right proof 1)
      | .isFalse proof =>
        .isFalse (by contrapose! proof; exact Nat.le_of_lt_succ proof)

#eval decideLE 2 5
#reduce decideLE 2 5

example : ∃ m : ℕ, m ≤ 10 ∧ (Nat.Prime (m^2 + m)) := by
  -- тактика `decide` для цели `g` запускает поиск инстанса для
  -- `Decidable g`, и в случае успеха проверяет что он
  -- построен конструктором `isTrue`, и возвращает доказательство
  -- то есть аргумент этого конструктора
  decide

example : ¬ ∃ x ≤ 5, ∃ y ≤ 5, ∃ z ≤ 5, x ^ 2 + y ^ 2 = z ^ 2 + 1144 := by
  decide

-- выражения if-then-else как
def foo (n m : Nat) : Nat :=
  if n ≤ m then
    5
  else
    2

-- на самом деле переписываются через `Decidable`:
def foo' (n m : Nat) : Nat :=
  match decideLE n m with
  | .isTrue _ => 5
  | .isFalse _ => 2
-- `decideLE` - это инстанс `Decidable (n ≤ m)` которых находится
-- поиском инстансов

-- в общем виде как-то так:
def ite' {α : Type} (P : Prop) (ifTrue : α) (ifFalse : α)
    [inst : Decidable P] : α :=
  match inst with
  | .isTrue _ => ifTrue
  | .isFalse _ => ifFalse

-- с неразрешимыми условиями if не работает
-- потому что непонятно как выполнять программу
def fermat (n : ℕ) : String :=
  if ∃ x y z : ℕ, x ^ n + y ^ n = z ^ n then
    "Exists!"
  else
    "Doesn't exists..."

-- но в математике можно сделать так:
open Classical in
noncomputable def fermat' (n : ℕ) : String :=
  if ∃ x y z : ℕ, x ^ n + y ^ n = z ^ n then
    "Exists!"
  else
    "Doesn't exists..."

-- в Classical есть инстанс делающий все предикаты разрешимыми
#check Classical.propDecidable
-- но он невычислимый, поэтому все что его использует тоже становится
-- noncomputable и нельзя выполнить #eval.
-- Но можно использовать в рассуждениях










/- ## Экстенсиональность -/

-- Аксиома `propext` говорит что если `P ↔ Q`, то `P = Q`
-- Это работает только для `Prop`
example (P Q : Prop) (h : P ↔ Q) : P = Q := by
  apply propext
  exact h

-- можно использовать тактику `ext`:
example (P Q : Prop) (h : P ↔ Q) : P = Q := by
  ext
  exact h

example {α β : Type} (f g : α → β) (h : ∀ a, f a = g a) : f = g := by
  ext a
  apply h

def f₁ (n : Nat) : Nat := 7

example : f₁ = f₁ := by rfl

example : f₁ = (fun x => 7) := by rfl

def f₂ (n : Nat) : Nat :=
  match n with
  | 0 => 7
  | m + 1 => f₂ m

example : f₁ = f₂ := by
  ext n
  induction n with
  | zero =>
    rfl
  | succ m ih =>
    simp [f₁, f₂]
    rw [← ih]
    simp [f₁]

/- ## Пример: max -/

namespace hidden

def max (a b : Int) : Int :=
  if a < b then
    b
  else
    a

theorem max_gt_left (a b : Int) : a ≤ max a b := by
  unfold max
  split_ifs with h
  · exact?
  · rfl

theorem max_gt_right (a b : Int) : b ≤ max a b := by
  unfold max
  split_ifs with h
  · rfl
  · exact?

/- ## Пример: List.sum -/

def List.sum (li : List Int) : Int :=
  match li with
  | [] => 0
  | hd :: tl => hd + List.sum tl

theorem List.sum_nil : List.sum [] = 0 := by
  unfold List.sum
  rfl

theorem List.sum_cons (hd : Int) (tl : List Int) :
    List.sum (hd :: tl) = hd + List.sum tl := by
  simp [sum]

end hidden















/- # Пример: возведение в степень -/

def slowPow (m n : Nat) : Nat :=
  match n with
  | 0 => 1
  | k + 1 => slowPow m k * m

def fastPow (m n : Nat) : Nat :=
  if n == 0 then
    1
  else
    let half := fastPow m (n / 2)
    if n % 2 == 0 then
      half * half
    else
      half * half * m
decreasing_by grind

theorem slowPow_add (m n k : ℕ) :
    slowPow m (n + k) = slowPow m n * slowPow m k := by
  induction k with
  | zero =>
    simp [slowPow]
  | succ k ih =>
    rw [← add_assoc]
    simp [slowPow]
    rw [ih]
    ring

theorem slowPow_eq_fastPow : slowPow = fastPow := by
  ext m n
  induction' n using Nat.strong_induction_on with k ih
  cases k with
  | zero =>
    simp [slowPow, fastPow]
  | succ k =>
    rw [fastPow]
    simp
    split_ifs with h_if
    · rw [← ih]
      · rw [← slowPow_add]
        congr 1
        grind
      · grind
    · simp [slowPow]
      left
      rw [← ih _ (by grind)]
      rw [← slowPow_add]
      congr
      grind




















/- # Пример: exactSqrt -/

def Nat.exactSqrtHelper (n m : Nat) : Option Nat :=
  if m * m = n then
    some m
  else
    match m with
    | 0 => none
    | k + 1 => Nat.exactSqrtHelper n k

def Nat.exactSqrt? (n : Nat) : Option Nat :=
  Nat.exactSqrtHelper n n

inductive ExactSqrtResult (n : Nat)
| found (m : Nat) (proof : m * m = n)
| notFound (proof : ¬ ∃ m, m * m = n)

inductive ExactSqrtHelperResult (n m : Nat)
| found (res : Nat) (proof : res * res = n)
| notFoundYet (proof : ∀ k, k ≤ m → k * k ≠ n)

def Nat.exactSqrtHelper' (n m : Nat) : ExactSqrtHelperResult n m :=
  if h : m * m = n then
    .found m h
  else
    match m with
    | 0 => .notFoundYet (by
        intro k hk
        simp at hk
        rw [hk]
        simp
        simp at h
        exact h
      )
    | k + 1 =>
      let prev := Nat.exactSqrtHelper' n k
      match prev with
      | .found res proof => .found res proof
      | .notFoundYet proof => .notFoundYet (by
          intro q hq
          by_cases hqk : q ≤ k
          · apply proof
            exact hqk
          · have hqk' : q = k + 1 := by omega
            rw [hqk']
            exact h
        )

def Nat.exactSqrt?' (n : Nat) : ExactSqrtResult n :=
  match Nat.exactSqrtHelper' n n with
  | .found res proof => .found res proof
  | .notFoundYet proof =>
    .notFound (by
      push_neg
      intro k
      by_cases hkn : k ≤ n
      · apply proof
        exact hkn
      simp at hkn
      suffices n < k * k by omega
      suffices k ≤ k * k by omega
      exact Nat.le_mul_self k
    )

def Nat.exactSqrtFrontend (n : Nat) : Option Nat :=
  match Nat.exactSqrt?' n with
  | .found res proof => .some res
  | .notFound proof => .none
