import Init

#eval "hello world"
#eval 2 + 2

/- 3.1 Begin -/
#check (2 + 2 : Nat)

def four : Nat := 2 + 2
def isOne (x : Nat) : String := if x = 1 then "yes" else "no"
#check four
#print four

#check isOne
#print isOne

def four' := 2 + 2
def isOne' x := if x = 1 then "yes" else "no"

#eval four
#eval isOne 3
#eval isOne 1
#eval four'
#eval isOne' 0

#eval IO.println "Hello, world!"

#check 2 + 2 = 4
#check 2 + 2 < 5
#check isOne 3 = "no"
#check 2 + 2 < 5 ∧ isOne 3 = "no"

def Fermat_statement : Prop := ∀ a b c n : Nat, a * b * c ≠ 0 ∧ n > 2 → a^n + b^n ≠ c^n

theorem two_plus_two_is_four : 2 + 2 = 4 := rfl
theorem Fermat_last_theorem : Fermat_statement := sorry

def foo n := 3 * n + 7

#eval foo 3
#eval foo (foo 3)

def bar n := foo (foo n) + 3

#eval bar 3
#eval bar (bar 3)

def printExample : IO Unit:= do
  IO.println "world"
  IO.println "hello"

#eval printExample

def factorial : Nat → Nat
  | 0       => 1
  | (n + 1) => (n + 1) * factorial n

#eval factorial 10
#eval factorial 100

def hanoi (numDisks start finish aux : Nat) : IO Unit :=
  match numDisks with
  | 0     => pure ()
  | n + 1 => do
      hanoi n start aux finish
      IO.println s!"Move disk {n + 1} from peg {start} to peg {finish}"
      hanoi n aux finish start

#eval hanoi 7 1 2 3

def addNums : List Nat → Nat
  | []      => 0
  | a::as => a + addNums as

#eval addNums [0, 1, 2, 3, 4, 5, 6]

#eval List.range 7


section
open List

#eval range 7
#eval addNums <| range 7
#eval map (fun x => x + 3) <| range 7
#eval foldl (.+.) 0 <| range 7

end


def myRange := List.range 7
#eval myRange.map fun x => x + 3


namespace hidden

def reverseAux : List α → List α → List α
  | [], r => r
  | (a::l), r => reverseAux l (a::r)

def reverse (as : List α) : List α := reverseAux as []

protected def append (as bs : List α) : List α := reverseAux as.reverse bs

#eval hidden.append [1, 2, 3] [4, 5, 6]
#eval hidden.append (bs := [1]) (as := [2])

def f (a : Nat) (b : Nat := 0) : Nat := a * a + b

end hidden

partial def gcd m n := if n = 0 then m else gcd n (m % n)
#eval gcd 45 30
#eval gcd 37252 49824

partial def bad (n : Nat) : Nat := bad (n + 1)

def fib' : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib' (n + 1) + fib' n

#eval fib' 5

def fibAux : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 => let p := fibAux n; (p.2, p.1 + p.2)

def fib n := (fibAux n).1

#eval (List.range 20).map fib

def fibListAux : Nat → List Nat
  | 0 => []
  | 1 => [0]
  | 2 => [1, 0]
  | n + 1 => let l := fibListAux n; (l[0]! + l[1]!)::l

def fibList n := (fibListAux n).reverse

#eval fibList 20

#print Option

def bar1 (n? : Option Nat) : Nat :=
  match n? with
    | some n => n
    | none   => 0

#eval bar1 (some 5)
#eval bar1 none
#print Option.getD
#eval (some 5).getD 0
#eval none.getD 0
/- 3.3 End -/

/- 3.4 Begin -/
def showSums : IO Unit := do
  let mut sum := 0
  for i in [0:100] do
    sum := sum + i
    IO.println s!"i: {i}, sum: {sum}"

#eval showSums

/-QUESTION: the keyword 'return' is not necessary? -/
/-QUESTION: else-branch is optional? -/
def isPrime (n : Nat) : Bool := Id.run do
  if n < 2 then false else
    for i in [2:n] do
      if n % i = 0 then
        return false
      if i * i > n then
        return true
    true

#eval (List.range 10000).filter isPrime

def bar2 (n? : Option Nat) : IO Unit := do
  let some n := n? |
    IO.println "oops"
  IO.println n

#eval bar2 (some 2)
#eval bar2 none

def primes (n : Nat) : Array Nat := Id.run do
  let mut result := #[]
  for i in [2:n] do
    if isPrime i then
      result := result.push i
  result

#eval (primes 10000).size

def a : Array Nat := #[1, 2]
#print a

def mulTable : Array (Array Nat) := Id.run do
  let mut table := #[]
  for i in [:10] do
    let mut row := #[]
    for j in [:10] do
      row := row.push ((i + 1) * (j + 1))
    table := table.push row
  table

#eval mulTable

def mulTable' : Array (Array Nat) := Id.run do
  let mut s := mkArray 10 (mkArray 10 0)
  for i in [:10] do
    for j in [:10] do
      s := s.set! i <| s[i]!.set! j ((i + 1) * (j + 1))
  s

#eval mulTable'

#eval show IO Unit from do
  for i in [:10] do
    for j in [:10] do
      let numstr := toString mulTable[i]![j]!
      -- print 1-3 spaces
      IO.print <| " ".pushn ' ' (3 - numstr.length)
      IO.print numstr
    IO.println ""
/- 3.4 End -/

/- 3.5 Exercises -/
/-1-/
def divs (n : Nat) : List Nat := (List.range n).filter (n % . = 0)

/-2-/
def perfect (n : Nat) : Bool := n = (addNums <| divs n)

def perfects (n : Nat) : List Nat := (List.range n).filter perfect
#eval perfects 1000

#eval 0::([1, 2] ++ [3])

/-3-/
def sublists : List α → List (List α)
  | [] => [[]]
  | (a::as) => let t := sublists as; t ++ t.map (fun x => a::x)

#eval sublists [1, 2, 3]

/-4-/
/- by induction. -/

/-5-/
def insertAux (a : α) (as : List α) : List (List α) :=
List.map (fun i => as.insertIdx i a) (List.range (as.length + 1))

def f (a : α) : List (List α) → List (List α)
  | [] => []
  | bs::bss => (insertAux a bs) ++ f a bss

#eval f 0 [[1, 2], [2, 1]]

def permutations : List α → List (List α)
  | [] => [[]]
  | (a::as) => f a <| permutations as

#eval permutations [1, 2, 3]

/-6-/
/- by induction; inductive step, note that there are n + 1 positions at which an
element can be inserted into a list of length n -/

/-7-/
/- not sure why no error when α is instantiated by Nat -/
def transpose [Inhabited α] (l : List (List α)) : List (List α) :=
List.map (fun i => List.map (fun vec => List.get! vec i) l)  (List.range (l.length))

def mat := [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
#eval transpose mat

/-8-/
def hanoi8 (numDisks start finish aux : Nat) : IO Unit :=
  match numDisks with
    | 0 => pure ()
    | n + 1 => do
      if start = 1
      then if finish = 2
           then /- finish = 2, aux = 3 -/
                hanoi8 n start aux finish
                IO.println s!"Move disk {n + 1} from peg {start} to peg {finish}"
                hanoi8 n aux finish start
           else /- finish = 3, aux = 2 -/
                hanoi8 n start finish aux
                IO.println s!"Move disk {n + 1} from peg {start} to peg {aux}"
                hanoi8 n finish start aux
                IO.println s!"Move disk {n + 1} from peg {aux} to peg {finish}"
                hanoi8 n start finish aux
      else if start = 2
           then if finish = 3
                then /- finish = 3, aux = 1 -/
                     hanoi8 n start aux finish
                     IO.println s!"Move disk {n + 1} from peg {start} to peg {finish}"
                     hanoi8 n aux finish start
                else /- finish = 1, aux = 3 -/
                     hanoi8 n start aux finish
                     IO.println s!"Move disk {n + 1} from peg {start} to peg {finish}"
                     hanoi8 n aux finish start
           else /- start = 3 -/
                if finish = 1
                then /- finish = 1, aux = 2 -/
                     hanoi8 n start finish aux
                     IO.println s!"Move disk {n + 1} from peg {start} to peg {aux}"
                     hanoi8 n finish start aux
                     IO.println s!"Move disk {n + 1} from peg {aux} to peg {finish}"
                     hanoi8 n start finish aux
                else /- finish = 2, aux = 1 -/
                     hanoi8 n start aux finish
                     IO.println s!"Move disk {n + 1} from peg {start} to peg {finish}"
                     hanoi8 n aux finish start

#eval hanoi8 3 1 2 3

/-9-/
def hanoi9 (numDisks start finish aux : Nat) : IO Unit :=
  match numDisks with
    | 0 => pure ()
    | n + 1 => do
      if start = 1
      then if finish = 2
           then /- finish = 2, aux = 3 -/
                hanoi9 n start aux finish
                IO.println s!"Move disk {n + 1} from peg {start} to peg {finish}"
                hanoi9 n aux finish start
           else /- finish = 3, aux = 2 -/
                hanoi9 n start finish aux
                IO.println s!"Move disk {n + 1} from peg {start} to peg {aux}"
                hanoi9 n finish start aux
                IO.println s!"Move disk {n + 1} from peg {aux} to peg {finish}"
                hanoi9 n start finish aux
      else if start = 2
      then if finish = 3
           then /- finish = 3, aux = 1 -/
                hanoi9 n start aux finish
                IO.println s!"Move disk {n + 1} from peg {start} to peg {finish}"
                hanoi9 n aux finish start
           else /- finish = 1, aux = 3 -/
                hanoi9 n start finish aux
                IO.println s!"Move disk {n + 1} from peg {start} to peg {aux}"
                hanoi9 n finish start aux
                IO.println s!"Move disk {n + 1} from peg {aux} to peg {finish}"
                hanoi9 n start finish aux
      else /- start = 3 -/
           if finish = 1
           then /- finish = 1, aux = 2 -/
                hanoi9 n start aux finish
                IO.println s!"Move disk {n + 1} from peg {start} to peg {finish}"
                hanoi9 n aux finish start
           else /- finish = 2, aux = 1 -/
                hanoi9 n start finish aux
                IO.println s!"Move disk {n + 1} from peg {start} to peg {aux}"
                hanoi9 n finish start aux
                IO.println s!"Move disk {n + 1} from peg {aux} to peg {finish}"
                hanoi9 n start finish aux

#eval hanoi9 3 1 2 3

/-10-/
namespace LbBinTree
inductive LbBinTree where
  | empty : LbBinTree
  | node  : Nat → LbBinTree → LbBinTree → LbBinTree
  deriving Repr, DecidableEq, Inhabited

def sum : LbBinTree → Nat
  | LbBinTree.empty => 0
  | LbBinTree.node n l r => n + sum l + sum r

def lt := LbBinTree.node 5 (LbBinTree.node 3 LbBinTree.empty LbBinTree.empty) (LbBinTree.node 1 (LbBinTree.node 2 LbBinTree.empty LbBinTree.empty) LbBinTree.empty)
#eval sum lt

def inorder (t : LbBinTree) : IO Unit :=
  match t with
    | LbBinTree.empty => pure ()
    | LbBinTree.node n l r => do
      inorder l
      IO.println s!"{n}"
      inorder r

#eval inorder lt

def preorder (t : LbBinTree) : IO Unit :=
  match t with
    | LbBinTree.empty => pure ()
    | LbBinTree.node n l r => do
      IO.println s!"{n}"
      preorder l
      preorder r

#eval preorder lt

def postorder (t : LbBinTree) : IO Unit :=
  match t with
    | LbBinTree.empty => pure ()
    | LbBinTree.node n l r => do
      postorder l
      postorder r
      IO.println s!"{n}"

#eval postorder lt
end LbBinTree

/-11-/
def pascal (n : Nat) : IO Unit :=
  match n with
    | 0 => pure ()
    | m + 1 => do
      let mut s := mkArray 1 1
      for i in [:m + 1] do
        if i ≠ 0 then IO.println ""
        --print s--
        for j in [:s.size] do
          if j ≠ 0 then IO.print ", "
          IO.print s[j]!
        --update s--
        s := s.push 1
        --s.size - 2, s.size - 3, ..., 2, 1
        --s.size - 1 - 1, ..., s.size - 1 - (s.size - 2)
        for j in [1:s.size - 1] do
          s := s.set! (s.size - 1 - j) (s[s.size - 1 - j]! + s[s.size - 2 - j]!)
      IO.println ""
#eval pascal 10
