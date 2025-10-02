#eval "Hello, world!"

#eval 2 + 2

def square (n : Nat) : Nat :=
  n * n

#eval square 7

#eval square 7 + 3
#eval square (7 + 3)

#eval square "hello"

def hello (name : String) :=
  String.append "Hello " name

#eval hello "Kitty"



#check 2 + 2
#check (2 + 2 : Int)

#check "Hello, world"

#check -2

#check (3e4 : Nat)

-- Nat → Nat
#check square

-- Nat
#check square 3


def addSquares (n : Nat) (m : Nat) : Nat :=
  n * n + m * m


#check addSquares

-- Nat → Nat → Nat
-- это
-- Nat → (Nat → Nat)

#check addSquares 3 5

#check addSquares 3

#eval (addSquares 3) 5

def squareAddNine : Nat → Nat := addSquares 3

-- squareAddNine m = addSquares 3 m

#check squareAddNine

#eval squareAddNine 2

-- x - вектор
-- (x, y) -- функция двух аргументов
-- (x, ·)

def addSquares' : Nat → Nat → Nat :=
  fun n m => n * n + m * m

#check fun (n : Nat) (m : Nat) => n * n + m * m

#check fun (n : Nat) => (fun (m : Nat) => n * n + m * m)

#check Nat
#check String
#check Type
#check Type 1
-- Type = Type 0 : Type 1 : Type 2 : ...
-- Type u - типы вселенной u

#check [1, 2, 3]

#check [(1 : Int), 2, 3]

#check List Nat

-- Type → Type
#check List

#check List Type

#check [Nat, Int, String]

#check (1, -1, "Lean")

#check Prod

#check Option

def foo : Option Nat := Option.some 3
def bar : Option Nat := Option.none

-- если head : α, tail : List α
-- то
-- List.cons head tail = лист присоединяющий head слева к tail
-- какой тип будет иметь List.cons?

#check List.cons

#check List.cons 42 [1, 2, 3]

#eval @List.cons Nat 42 [1, 2, 3]

def oneStepToZero (n : Int) : Int :=
  if n < 0 then
    n + 1
  else if n > 0 then
    n - 1
  else
    0

#eval oneStepToZero 3
#eval oneStepToZero (-3)

def isEmpty (li : List Nat) : Bool :=
  match li with
  | [] => true
  | List.cons head tail => false

def isEmptyOrHeadEven (li : List Nat) : Bool :=
  match li with
  | [] => true
  | List.cons head tail =>
    head % 2 == 0
    -- if head % 2 == 0 then
    --   true
    -- else
    --   false

#eval isEmpty [1]
#eval isEmptyOrHeadEven [2, 24, 224]

#check List.find?

#eval List.find? (fun n => n % 2 == 0) [1, 2, 3, 4]
#eval List.find? (fun n => n % 2 == 0) [1, 3, 5]

def myFind {α : Type} (p : α → Bool) (li : List α) : Option α :=
  match li with
  | [] => Option.none
  | List.cons head tail =>
    if p head then
      Option.some head
    else
      myFind p tail

#eval myFind (fun n => n % 2 == 0) [1, 2, 3, 4]
#eval myFind (fun n => n % 2 == 0) [1, 3, 5]
