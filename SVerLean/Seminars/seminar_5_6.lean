import Mathlib

set_option linter.hashCommand false

/- # Кванторы -/

example : ∀ n m, n + m = 0 → n = 0 := by
  sorry

example (f : ℤ → ℤ) (h : ∀ n, n < f n) : 4 < f (f 3) := by
  sorry

example {α : Type} (P : α → Prop) (h : ∃ a, ¬ P a) : ¬ ∀ a, P a := by
  sorry

example : ∃ li : List ℕ, li.length > 2 ∧ li.reverse = li := by
  sorry

/- # Индукция -/

example (f : ℕ → ℕ) (h : ∀ n, f (n + 1) > f n) : ∀ n, f n ≥ n := by
  sorry

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

def ArithExpr.eval (e : ArithExpr) (env : String → Int) : Int :=
  sorry

def ArithExpr.simplifyNum (e : ArithExpr) : ArithExpr :=
  sorry

#guard expr₁.eval (fun _ => 3) == 4
#guard expr₂.eval (fun _ => 3) == -6
#guard expr₃.eval (fun name => match name with | "x" => 3 | "y" => -2 | _ => 0) == 0
#guard simplifyNum (.add (.mul (.var "x") (.add (.num 1) (.mul (.num 2) (.num 3)))) (.sub (.num 5) (.num 4))) ==
  .add (.mul (.var "x") (.num 7)) (.num 1)

theorem simplifyNum_eval_eq_eval (expr : ArithExpr) (env : String → Int) :
    expr.simplifyNum.eval env = expr.eval env := by
  sorry

/- # Числа Фибоначчи -/

def fib (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

def fastFib (n : Nat) : Nat :=
  go 1 1 n
where go (x y : Nat) (stepsLeft : Nat) :=
  match stepsLeft with
  | 0 => x
  | stepsLeftNew + 1 =>
    go y (x + y) stepsLeftNew

theorem fastFib_go_eq_fibs (n stepsLeft : Nat) :
    fastFib.go (fib n) (fib (n + 1)) stepsLeft = fib (n + stepsLeft) := by
  sorry

theorem fastFib_eq_fib : fastFib = fib := by
  sorry

/- # Разрешимость -/

/- P.S.: если это скучно, сделайте инстанс ниже -/
instance (P : Nat → Prop) [inst : ∀ n, Decidable (P n)] (m : Nat) :
    Decidable (∃ n, n ≤ m ∧ P n) :=
  sorry

example : ∀ k ≤ 15, ∃ a ≤ k, ∃ b ≤ k, ∃ c ≤ k, ∃ d ≤ k,
    k = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  decide

example : ∀ k ≤ 100, ∃ a ≤ k, ∃ b ≤ k, ∃ c ≤ k, ∃ d ≤ k,
    k = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  decide +native

instance (P : Nat → Nat → Prop) [inst : ∀ n m, Decidable (P n m)] (m : Nat) :
    Decidable (∃ x y, x + y = m ∧ P x y) :=
  sorry

example : ∀ k ≤ 10, ∃ x y, x + y = k ∧ Nat.Prime (x^2 + y^2 + 5) := by
  decide

/- # Правильные скобочные последовательности -/

namespace hidden

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

theorem CorrectBS.insertBetween {left right : List Bracket} (h : CorrectBS (left ++ right)) :
    CorrectBS (left ++ [.op, .cl] ++ right) := by
  sorry -- не нужно делать

/- Стандартный алгоритм проверки скобочной последовательности на правильность.
```py
def check(bs):
  balance = 0
  for b in bs:
    if b == '(':
      balance += 1
    else:
      balance -= 1
      if balance < 0:
        return False
  return balance == 0
```
как обычно цикл `for` переписываем через рекурсию
-/
def check (bs : List Bracket) : Bool :=
  go bs 0
where
  go (bs : List Bracket) (balance : ℕ) : Bool :=
    match bs with
    | [] => balance == 0
    | .op :: tail =>
      go tail (balance + 1)
    | .cl :: tail =>
      match balance with
      | 0 => false
      | newInit + 1 =>
        go tail newInit

-- Подсказка: понадобится `induction ... generalizing`
theorem check_go_append {left right : List Bracket} {a b : ℕ}
    (h_left : check.go left a = true) (h_right : check.go right b = true) :
    check.go (left ++ right) (a + b) = true := by
  sorry

theorem check_of_correct_eq_true {bs : List Bracket} (h : CorrectBS bs) :
    check bs = true := by
  sorry

-- Смысл: если `go bs balance` выдает `true`, то `((...(bs` (где слева `balance` открывающих
-- скобок) должна быть правильной.
-- Подсказка: попробуйте `fun_induction`
-- Подсказка 2: используйте `CorrectBS.insertBetween`
theorem correct_append_of_check_go_eq_true {bs : List Bracket} {balance : ℕ}
    (h : check.go bs balance = true) :
    CorrectBS (List.replicate balance .op ++ bs) := by
  sorry

theorem correct_of_check_eq_true {bs : List Bracket} (h : check bs = true) :
    CorrectBS bs := by
  sorry

-- осталось все вместе скомбинировать
instance (bs : List Bracket) : Decidable (CorrectBS bs) :=
  sorry

inductive Tree
| leaf
| node (children : List Tree)

def Tree.toBS (tree : Tree) : List Bracket :=
  match tree with
  | .leaf => [.op, .cl]
  | .node children => .op :: children.flatMap (fun child => child.toBS) ++ [.cl]

theorem Tree.toBS_correct (tree : Tree) : CorrectBS tree.toBS := by
  sorry

end hidden

/- # Разрешимость 2: возрастающие функции

В этой задаче мы покажем разрешимость уравнений `f x = y`
для строго монотонной функции f.

Это обощение предикатов `IsSquare` и `IsPow`
-/

/-- Тайпкласс для строго возрастающих функций -/
class StrictMonotoneFun (f : ℕ → ℕ) where
  proof : ∀ n m, n < m → f n < f m

/-- В Матлибе есть предикат `StrictMono` означающий то же самое.
Мы создали для этого тайпкласс чтобы он выводился при помощи typeclass
search. А это функция которая позваляет использовать
`StrictMono` чтобы создать `StrictMonotoneFun` (см. ниже). -/
theorem StrictMonotoneFun_iff_StrictMono (f : ℕ → ℕ) :
    StrictMono f ↔ StrictMonotoneFun f := by
  constructor
  · intro h
    exact ⟨h⟩
  · intro h
    exact h.proof

instance : StrictMonotoneFun id where
  proof := by simp

instance (n : Nat) [NeZero n] : StrictMonotoneFun (fun x ↦ x ^ n) := by
  rw [← StrictMonotoneFun_iff_StrictMono]
  apply Nat.pow_left_strictMono
  exact Ne.symm (NeZero.ne' n)

instance (f g : ℕ → ℕ) [StrictMonotoneFun f] [StrictMonotoneFun g] :
    StrictMonotoneFun (fun x ↦ f x + g x) :=
  sorry

instance (f g : ℕ → ℕ) [StrictMonotoneFun f] [StrictMonotoneFun g] :
    StrictMonotoneFun (fun x ↦ f x * g x) :=
  sorry

instance (f : ℕ → ℕ) [StrictMonotoneFun f] (y : ℕ) :
    Decidable (∃ x, f x = y) :=
  sorry

example : ∃ x, x ^ 2 + x ^ 3 = 12 := by
  decide
