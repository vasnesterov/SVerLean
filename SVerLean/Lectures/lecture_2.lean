-- импорты: пригодятся нам в самом конце
import Std.Data.HashSet.Basic
import Std.Data.HashSet.Lemmas

structure Point where
  x : Int
  y : Int

#check Point
#check Point.x

def pt₁ : Point :=
  {
    x := 1
    y := 2
  }

def pt₂ : Point := ⟨-3, 4⟩

#eval Point.x pt₁
-- "Dot notation":
-- Если `pt₁` имеет тип `Point`, тогда `pt₁.someMethod` это
-- синтаксический сахар для `Point.someMethod pt₁`
-- (если `Point.someMethod` принимает много аргументов, то `pt₁`
-- подставляется
-- в первых из них, имеющий тип `Point`)
#eval pt₁.x

def Point.add (p₁ p₂ : Point) : Point :=
  {
    x := p₁.x + p₂.x
    y := p₁.y + p₂.y
  }

def Point.rotate (p : Point) : Point :=
  { x := p.y, y := -p.x }

def Point.add' (p₁ p₂ : Point) : Point :=
  ⟨p₁.x + p₂.x, p₁.y + p₂.y⟩

def Point.add'' (p₁ p₂ : Point) : Point :=
  match p₁, p₂ with
  | ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ => ⟨x₁ + x₂, y₁ + y₂⟩

def Point.add''' : Point → Point → Point :=
  fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ => ⟨x₁ + x₂, y₁ + y₂⟩

#eval Point.add pt₁ pt₂
#eval pt₁.add pt₂
#eval pt₁.rotate
#eval pt₁.rotate.add pt₂

-------------------------------------------------------

structure Node where
  address : String
  alive : Bool
deriving Repr, BEq, Hashable

structure Connection where
  source : Node
  destination : Node
  capacity : Int
deriving Repr

structure Network where
  nodes : Array Node
  connections : Array Connection
deriving Repr

namespace Network

def empty : Network :=
  {
    nodes := #[]
    connections := #[]
  }

-- можно использовать `where`
def empty' : Network where
  nodes := #[]
  connections := #[]

def insertNode (network : Network) (node : Node) : Network where
  nodes := network.nodes.push node
  connections := network.connections

-- можно "обновлять" только определенные поля
def insertNode' (network : Network) (node : Node) : Network :=
  { network with nodes := network.nodes.push node }

def insertConnection (connection : Connection)
    (network : Network) : Network :=
  { network with connections := network.connections.push connection }

#eval Network.empty

def node₁ : Node := { address := "192.168.1.1", alive := true }
def node₂ : Node := { address := "192.168.1.2", alive := true }
def connection : Connection :=
  { source := node₁, destination := node₂, capacity := 100 }

def singleNodeNetwork := Network.empty.insertNode node₁
#eval singleNodeNetwork
def twoNodeNetwork := singleNodeNetwork.insertNode node₂
def twoNodeConnected := twoNodeNetwork.insertConnection connection

def isConnected (network : Network) (sourceAddress targetAddress : String) : Bool :=
  let sourceNode? : Option Node := network.nodes.find? (fun n => n.address == sourceAddress && n.alive)
  match sourceNode? with
  | none => false
  | some sourceNode =>
    let targetNode? := network.nodes.find? (fun n => n.address == targetAddress && n.alive)
    match targetNode? with
    | none => false
    | some targetNode =>
      let connection? := network.connections.find?
        (fun c => c.source == sourceNode && c.destination == targetNode)
      -- match connection? with
      -- | none => false
      -- | some _ => true
      connection?.isSome

#eval twoNodeConnected.isConnected "192.168.1.1" "192.168.1.2"

end Network










namespace Hidden

inductive Bool : Type
| tr : Bool  -- true
| fal : Bool -- false

#check Bool

#check Bool.tr
#check Bool.fal

def Bool.toNat (b : Bool) : Nat :=
  match b with
  | tr => 1
  | fal => 0

inductive Weekday : Type
| monday : Weekday
| tuesday : Weekday
| wednesday : Weekday
| thursday : Weekday
| friday : Weekday
| saturday : Weekday
| sunday : Weekday

inductive Weekday'
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday

inductive Unit
| u

inductive Empty

#check Weekday'.monday

inductive Color
| rgb (r g b : Float)
| monochrome (v : Float)

inductive Color'
| rgb : Float → Float → Float → Color'
| monochrome : Float → Color'

#check Color.rgb 1.0 0.3 0.2
#check Color.monochrome 0.5

def Color.toMonochrome (c : Color) : Color :=
  match c with
  | rgb r ggg b => monochrome ((r + ggg + b) / 3)
  | monochrome v => monochrome v

inductive Nat : Type
| zero : Nat
| succ (n : Nat) : Nat -- n ↦ n + 1

#check Nat
#check Nat.zero
#check Nat.succ

#check Nat.succ (Nat.succ Nat.zero) -- 2
#check Nat.zero.succ.succ

def Nat.pred (n : Nat) : Nat :=
  match n with
  | zero => zero
  | succ m => m

#eval Nat.zero.succ.succ.pred

def Nat.isEven (n : Nat) : _root_.Bool :=
  match n with
  | zero => true
  | succ m => (Nat.isEven m).not

inductive List (α : Type) : Type
| nil
| cons (head : α) (tail : List α)

def List.sum (xs : List Int) : Int :=
  match xs with
  | nil => 0
  | cons head tail => head + tail.sum

inductive Vector' (α : Type) (n : Nat)
| nil : Vector' α Nat.zero
| cons (n : Nat) (head : α) (tail : Vector' α n) : Vector' α (Nat.succ n)

-- `Vector α n` - тип массивов элементов `α` фиксированной длины `n`
inductive Vector (α : Type) : Nat → Type
| nil : Vector α Nat.zero
| cons {n : Nat} (head : α) (tail : Vector α n) : Vector α n.succ

-- #check Vector.nil
#check Vector Int Nat.zero.succ

#check (Vector.nil : Vector Nat Nat.zero)
#check Vector.cons "first" (Vector.nil : Vector String Nat.zero)

mutual
  inductive Even
  | even_zero : Even
  | even_succ (n : Odd) : Even

  inductive Odd
  | odd_succ (n : Even) : Odd
end

mutual

  def Even.toNat (e : Even) : Nat :=
    match e with
    | Even.even_zero => Nat.zero
    | Even.even_succ n => Nat.succ (Odd.toNat n)

  def Odd.toNat (o : Odd) : Nat :=
    match o with
    | Odd.odd_succ n => Nat.succ (Even.toNat n)

end

inductive Foo : Type
| nil : Foo
| bar (x : Nat → Foo) : Foo

#check Foo.nil
#check Foo.bar (fun n => Foo.nil)

#check Foo.bar (fun n =>
  match n with
  | Nat.zero => Foo.nil
  | Nat.succ m => Foo.bar (fun k => Foo.nil)
)

mutual
  inductive ListTree
  | nil
  | cons (head : Tree) (tail : ListTree)

  inductive Tree : Type
  | leaf : Tree
  | node (children : ListTree) : Tree
end

end Hidden

-----------------------------------------------------------------------------------------

def fib (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

#eval [fib 0, fib 1, fib 2, fib 3, fib 4, fib 5]

-- #eval fib 300
#eval 2^300

/-
```py
def fib(n):
  fibs = [1, 1]
  while len(fibs) < n:
    fibs.append(fibs[-1] + fibs[-2])
  return fibs[n - 1]
```
-/

def fibHelper (n : Nat) (fibs : Array Nat) : Array Nat :=
  if fibs.size ≥ n then
    fibs
  else
    let newFibs := fibs.push (fibs[fibs.size - 1]! + fibs[fibs.size - 2]!)
    fibHelper n newFibs

def fib' (n : Nat) : Nat :=
  let fibs : Array Nat := #[1, 1]
  let newFibs := fibHelper n fibs
  newFibs[n - 1]!

#eval fib' 300

-- для вспомогательных функций стоит использовать `where`
def fib'' (n : Nat) : Nat :=
  let fibs : Array Nat := #[1, 1]
  let newFibs := fibHelper' n fibs
  newFibs[n - 1]!
where
  fibHelper' (n : Nat) (fibs : Array Nat) : Array Nat :=
  if fibs.size ≥ n then
    fibs
  else
    let newFibs := fibs.push (fibs[fibs.size - 1]! + fibs[fibs.size - 2]!)
    fibHelper n newFibs


def binSearchSquareRoot (n left right : Nat) : Nat :=
  if right - left ≤ 1 then
    left
  else
    let middle := (left + right) / 2
    if middle * middle ≤ n then
      binSearchSquareRoot n middle right
    else
      binSearchSquareRoot n left middle
termination_by right - left

namespace Network

/-

```py
def isNodesReachableHelper(src, tar, availableNodes):
  if src == tar:
    return True
  if (src, tar) in network.connections:
    return True
  for middleNode in network.nodes:
    if middleNode in availableNodes:
      availableNodes.erase(middleNode)
      reachable1 = isNodesReachableHelper(src, middleNode, availableNodes)
      reachable2 = isNodesReachableHelper(middleNode, tar, availableNodes)
      if reachable1 and reachable2:
        return True
      availableNodes.insert(middleNode)
  return False

def isNodesReachable(src, tar):
    return isNodesReachableHelper(src, tar, set(network.nodes))
```

-/

mutual

def isNodesReachableHelperFor (network : Network) (sourceNode targetNode : Node)
    (availableNodes : Std.HashSet Node) (idx : Nat) : Bool :=
  if h : idx ≥ network.nodes.size then
    false
  else
    let middleNode := network.nodes[idx]
    if availableNodes.contains middleNode then
      have : (availableNodes.erase network.nodes[idx]).size < availableNodes.size := sorry
      let newAvailableNodes := availableNodes.erase middleNode
      let reachable₁ := network.isNodesReachableHelper sourceNode middleNode newAvailableNodes
      let reachable₂ := network.isNodesReachableHelper middleNode targetNode newAvailableNodes
      if reachable₁ && reachable₂ then
        true
      else
        network.isNodesReachableHelperFor sourceNode targetNode availableNodes (idx + 1)
    else
      network.isNodesReachableHelperFor sourceNode targetNode availableNodes (idx + 1)
termination_by (availableNodes.size, network.nodes.size - idx)

def isNodesReachableHelper (network : Network) (sourceNode targetNode : Node)
    (availableNodes : Std.HashSet Node) : Bool :=
  if sourceNode == targetNode then
    true
  else if network.connections.any (fun c => c.source == sourceNode && c.destination == targetNode) then
    true
  else
    network.isNodesReachableHelperFor sourceNode targetNode availableNodes 0
termination_by (availableNodes.size, network.nodes.size + 1)

end

def getNode? (network : Network) (address : String) : Option Node :=
  network.nodes.find? (fun n => n.address = address && n.alive)

def isReachable (network : Network) (sourceAddress targetAddress : String) : Bool :=
  let sourceNode? := getNode? network sourceAddress
  match sourceNode? with
  | none => false
  | some sourceNode =>
  let targetNode? := getNode? network targetAddress
  match targetNode? with
  | none => false
  | some targetNode =>
  network.isNodesReachableHelper sourceNode targetNode (Std.HashSet.ofArray network.nodes)

namespace Test

def node₁ : Node := ⟨"1", true⟩
def node₂ : Node := ⟨"2", true⟩
def node₃ : Node := ⟨"3", true⟩
def node₄ : Node := ⟨"4", true⟩
def node₅ : Node := ⟨"5", true⟩
def node₆ : Node := ⟨"6", true⟩

def con₁ : Connection := ⟨node₁, node₃, 100⟩
def con₂ : Connection := ⟨node₂, node₃, 100⟩
def con₃ : Connection := ⟨node₃, node₄, 100⟩
def con₄ : Connection := ⟨node₄, node₅, 100⟩
def con₅ : Connection := ⟨node₆, node₄, 100⟩

def network : Network :=
  ⟨#[node₁, node₂, node₃, node₄, node₅, node₆], #[con₁, con₂, con₃, con₄, con₅]⟩

#eval! network.isReachable "1" "1"

#eval! network.isReachable "1" "5"

#eval! network.isReachable "1" "6"

#eval! network.isReachable "6" "1"

end Test

end Network
