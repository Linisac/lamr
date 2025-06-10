import LAMR.Util.Propositional

--$5.1
namespace hidden
inductive PropForm where
  | tr     : PropForm
  | fls    : PropForm
  | var    : String → PropForm
  | conj   : PropForm → PropForm → PropForm
  | disj   : PropForm → PropForm → PropForm
  | impl   : PropForm → PropForm → PropForm
  | neg    : PropForm → PropForm
  | biImpl : PropForm → PropForm → PropForm
  deriving Repr, DecidableEq
end hidden

#print hidden.PropForm
open hidden.PropForm
#check (impl (conj (var "p") (var "q")) (var "r"))
--#check prop!{p ∧ q → (r ∨ ¬ p) → q}
--#check prop!{p ∧ q ∧ r → p}

def propExample := prop!{p ∧ q → r ∧ p ∨ ¬ s1 → s2 }
#print propExample
#eval propExample
#eval toString propExample

namespace PropForm

def complexity : PropForm → Nat
  | var _      => 0
  | tr         => 0
  | fls        => 0
  | neg A      => complexity A + 1
  | conj A B   => complexity A + complexity B + 1
  | disj A B   => complexity A + complexity B + 1
  | impl A B   => complexity A + complexity B + 1
  | biImpl A B => complexity A + complexity B + 1

def depth : PropForm → Nat
  | var _      => 0
  | tr         => 0
  | fls        => 0
  | neg A      => depth A + 1
  | conj A B   => Nat.max (depth A) (depth B) + 1
  | disj A B   => Nat.max (depth A) (depth B) + 1
  | impl A B   => Nat.max (depth A) (depth B) + 1
  | biImpl A B => Nat.max (depth A) (depth B) + 1

def vars : PropForm → List String
  | var s      => [s]
  | tr         => []
  | fls        => []
  | neg A      => vars A
  | conj   A B => (vars A).union' (vars B)
  | disj   A B => (vars A).union' (vars B)
  | impl   A B => (vars A).union' (vars B)
  | biImpl A B => (vars A).union' (vars B)

#eval complexity propExample
#eval depth propExample
#eval vars propExample

end PropForm

#eval PropForm.complexity propExample
#eval propExample.complexity

def PropForm.eval (v : PropAssignment) : PropForm → Bool
  | var s => v.eval s
  | tr    => true
  | fls   => false
  | neg A => !(eval v A)
  | conj A B => (eval v A) && (eval v B)
  | disj A B => (eval v A) || (eval v B)
  | impl A B => !(eval v A) || (eval v B)
  | biImpl A B => (!(eval v A) || (eval v B)) && (!(eval v B) || (eval v A))

#eval let v := PropAssignment.mk [("p", true), ("q", true), ("r", true)]
      propExample.eval v

#check propassign!{p, q, r}
#eval propExample.eval propassign!{p, q, r}

def allSublists : List α → List (List α)
  | [] => [[]]
  | (a :: as) =>
    let recval := allSublists as
    recval.map (a :: .) ++ recval

#eval allSublists propExample.vars

def truthTable (A : PropForm) : List (List Bool × Bool) :=
  let vars := A.vars
  let assignments := (allSublists vars).map (fun l => PropAssignment.mk (l.map (., true)))
  let evalLine := fun v : PropAssignment => (vars.map v.eval, A.eval v)
  assignments.map evalLine

#eval truthTable propExample
def v := propExample.vars
#eval v
def a := (allSublists v).map (fun l => PropAssignment.mk (l.map (., true)))
#eval a

def PropForm.isValid (A : PropForm) : Bool := List.all (truthTable A) Prod.snd
def PropForm.isSat(A : PropForm) : Bool := List.any (truthTable A) Prod.snd

#eval propExample.isValid
#eval propExample.isSat
