
namespace hidden

def List.mySum {α : Type} (li : List α) : α :=
  match li with
  | [] => 0
  | head :: tail => head + tail.mySum

def double {α : Type} (add : α → α → α) (a : α) : α :=
  add a a

#eval double Nat.add 3

#eval double Int.add (-3)

#eval double Float.add 1.25

def List.mySum' {α : Type} (zero : α) (add : α → α → α) (li : List α) : α :=
  match li with
  | [] => zero
  | head :: tail => add head (List.mySum' zero add tail)

structure Add (α : Type) where
  add : α → α → α

def double' {α : Type} (howToAdd : Add α) (a : α) : α :=
  howToAdd.add a a

structure AddZero (α : Type) where
  add : α → α → α
  zero : α

def List.mySum'' {α : Type} (s : AddZero α) (li : List α) : α :=
  match li with
  | [] => s.zero
  | head :: tail => s.add head (List.mySum'' s tail)

class Add' (α : Type) where
  add : α → α → α

def double'' {α : Type} [inst : Add' α] (a : α) : α :=
  inst.add a a

instance Nat.Add' : Add' Nat where
  add := Nat.add

-- def three : Nat := 3
#eval double'' (3 : Nat)

instance Int.Add' : Add' Int where
  add := Int.add

#eval double'' (3 : Int)

class LT (α : Type) where
  lt : α → α → Bool

def isSorted {α : Type} [inst : LT α] (li : List α) : Bool := sorry

def minimum? {α : Type} [inst : LT α] (li : List α) : Option α := sorry

end hidden

#check List.sum

namespace hidden

def sort {α : Type} [inst : LT α] (li : List α) : List α := sorry

class LinearOrder (α : Type) where
  lt : α → α → Bool
  antisymm : ∀ x y : α, lt x y = true → lt y x = false
  trans : ∀ x y z : α, lt x y = true ∧ lt y z = true → lt x z = true

class LinearOrder' (α : Type) extends LT α where
  antisymm : ∀ x y : α, lt x y = true → lt y x = false
  trans : ∀ x y z : α, lt x y = true ∧ lt y z = true → lt x z = true


class Inhabited (α : Type) where
  default : α

def Array.myGet! {α : Type} [inst : Inhabited α] (arr : Array α) (idx : Nat) : α :=
  if h : idx < arr.size then
    arr[idx]
  else
    inst.default

instance : Inhabited Nat where
  default := 123

instance : Inhabited Bool where
  default := false

instance : Inhabited String where
  default := ""

instance (α : Type) : Inhabited (Option α) where
  default := .none

#eval Array.myGet! #[Option.none, Option.some 3] 123

instance (α β : Type) [instA : Inhabited α] [instB : Inhabited β] : Inhabited (α × β) where
  default := (instA.default, instB.default)

#eval Array.myGet! #[(false, 12), (true, 18)] 1000

def add {α : Type} [inst : Add' α] (x y : α) : α := inst.add x y

infix:60 " +++ " => fun l r => add l r

#eval (3 : Nat) +++ (3 : Nat)

end hidden

inductive Pos
| one : Pos
| succ : Pos → Pos

def Pos.toNat (p : Pos) : Nat :=
  match p with
  | one => Nat.succ Nat.zero
  | succ q => Nat.succ q.toNat

def Nat.toPos (n : Nat) : Pos :=
  match n with
  | 0 => Pos.one
  | 1 => Pos.one
  | n + 2 => Pos.succ (Nat.toPos (n + 1))

#eval Nat.toPos 3

def two : Pos := 2

-- instance (n : Nat) : OfNat Pos n where
--   ofNat := Nat.toPos n

-- def two' : Pos := 2

-- #eval two'

instance (n : Nat) [NeZero n] : OfNat Pos n where
  ofNat := Nat.toPos n

def zero : Pos := 0

def two' : Pos := 2

instance : ToString Pos where
  toString (p : Pos) := toString p.toNat

#eval Nat.add two' two'

def one : Nat := 1

#eval Int.add one one

instance : Coe Pos Nat where
  coe (p : Pos) : Nat := p.toNat

#eval Nat.add two' two'

#eval Int.add two' one