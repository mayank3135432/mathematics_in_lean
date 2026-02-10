import Lean
open Lean Meta Widget
open Std
/-- Possible runtime errors. -/
inductive Error
  | varNotFound (x : String)
  | notAFunction (e : String)
  | badPrimitive (e : String)
  | operationOnWrongType (e t : String)
  | divByZero
deriving Repr
instance : ToString Error where
  toString
    | Error.varNotFound x         => s!"variable {x} not found"
    | Error.notAFunction e      => s!"{e} is not a function"
    | Error.badPrimitive e      => s!"{e} is not a valid primitive"
    | Error.operationOnWrongType e t => s!"operation {e} on wrong type {t}"
    | Error.divByZero             => "division by zero"
inductive PrimOp
  | add
  | sub
  | mul
  | div
  | eq
deriving Repr, BEq

instance : ToString PrimOp where
  toString
    | .add => "+"
    | .sub => "-"
    | .mul => "*"
    | .div => "/"
    | .eq  => "=="
/-- Syntax for λ-calculus expressions. -/
inductive LambdaCalc where
  | const (n : Int)
  | var (x : String)
  | lam (x : String) (body : LambdaCalc)
  | app (e₁ e₂ : LambdaCalc)
  | appPrim (prim : PrimOp) (e₁ e₂ : LambdaCalc)
  | letIn (x : String) (e₁ e₂ : LambdaCalc)

deriving Repr
def lambdaCalcToString : LambdaCalc → String
  | .const n => toString n
  | .var x => x
  | .lam x e => s!"(λ {x}. {lambdaCalcToString e})"
  | .app e₁ e₂ => s!"(@ {lambdaCalcToString e₁} {lambdaCalcToString e₂})"
  | .appPrim prim e₁ e₂ => s!"({prim} {lambdaCalcToString e₁} {lambdaCalcToString e₂})"
  | .letIn x e₁ e₂ => s!"(let [{x} {lambdaCalcToString e₁}] {lambdaCalcToString e₂})"
instance : ToString LambdaCalc where
  toString := lambdaCalcToString
/- change repr to show full AST Tree but not as a String -/
instance : Repr LambdaCalc where
  reprPrec e _ := toString e
/- Value domain: numbers, closures, and primitives. -/
inductive Value : Type where
  | num  (n : Int)
  | clo  (x : String) (body : LambdaCalc) (env : List (String × Value))
  | prim (p : PrimOp)
deriving Repr, Nonempty
instance : ToString Value where
  toString
    | .num n => toString n
    | .clo x _ _ => s!"<closure {x}>"
    | .prim p => s!"<prim {p}>"
/-- Environment is a list of variable bindings.
Alternately, we could use other data structures;
-/
abbrev Env := List (String × Value)
/-- Lookup in environment. -/
def lookup (env : Env) (x : String) : Except Error Value :=
  match env.find? (fun p => p.fst = x) with
  | some (_, v) => Except.ok v
  | none =>
    match x with
    | "+" => Except.ok (Value.prim .add)
    | "-" => Except.ok (Value.prim .sub)
    | "*" => Except.ok (Value.prim .mul)
    | "/" => Except.ok (Value.prim .div)
    | "==" => Except.ok (Value.prim .eq)
    | _     => Except.error (Error.varNotFound x)
/-- Apply a primitive to Int arguments.
    Here: +, -, *, /, == are primitives from Lean.
-/
def applyPrim (p : PrimOp) (args : List Value) : Except Error Value := do
  let ns ← args.mapM fun
    | .num n => pure n
    | _ => Except.error (.badPrimitive s!"Non-numeric argument for {p}")
  match p, ns with
  | .add, [a,b] => pure (.num (a + b))
  | .sub, [a,b] => pure (.num (a - b))
  | .mul, [a,b] => pure (.num (a * b))
  | .div, [a,b] => if b == 0 then Except.error .divByZero else pure (.num (a / b))
  | .eq,  [a,b] => pure (.num (if a == b then 1 else 0))
  | _, _ => Except.error (.badPrimitive s!"wrong arity for {p}")
partial def eval (env : Env) : LambdaCalc → Except Error Value
  | .const n => pure (.num n)
  | .var x   => lookup env x
  | .lam x e => pure (.clo x e env)
  | .app e₁ e₂ => do
      let v₁ ← eval env e₁
      let v₂ ← eval env e₂
      match v₁ with
      | .clo x body cloEnv =>
        eval ((x,v₂)::cloEnv) body
      | .prim p => Except.error (.notAFunction (s!"primitive {p}"))
      | _ => Except.error (.notAFunction (toString v₁))
  | .appPrim prim e₁ e₂ => do
      let v₁ ← eval env e₁
      let v₂ ← eval env e₂
      applyPrim prim [v₁, v₂]
  | .letIn x e₁ e₂ => do
      let v₁ ← eval env e₁
      eval ((x,v₁)::env) e₂
/-- Pretty printer for result. -/
def evalPP (e : LambdaCalc) : String :=
  match eval [] e with
  | .ok v => s!"Result: {v}"
  | .error err => s!"Error: {err}"
declare_syntax_cat LambdaCalcSyntax
syntax num : LambdaCalcSyntax
syntax ident : LambdaCalcSyntax
syntax str : LambdaCalcSyntax
syntax "(" LambdaCalcSyntax ")" : LambdaCalcSyntax
syntax "λ" ident "." LambdaCalcSyntax : LambdaCalcSyntax
syntax "@" LambdaCalcSyntax LambdaCalcSyntax : LambdaCalcSyntax
syntax:65 LambdaCalcSyntax:65 "+" LambdaCalcSyntax:66 : LambdaCalcSyntax
syntax:65 LambdaCalcSyntax:65 "-" LambdaCalcSyntax:66 : LambdaCalcSyntax
syntax:70 LambdaCalcSyntax:70 "*" LambdaCalcSyntax:71 : LambdaCalcSyntax
syntax:70 LambdaCalcSyntax:70 "/" LambdaCalcSyntax:71 : LambdaCalcSyntax
syntax:50 LambdaCalcSyntax:50 "==" LambdaCalcSyntax:51 : LambdaCalcSyntax
syntax "let" "[" ident LambdaCalcSyntax "]" LambdaCalcSyntax : LambdaCalcSyntax


syntax "`[LC| " LambdaCalcSyntax "]" : term
macro_rules
  | `(`[LC| $n:num]) => `(LambdaCalc.const $n)
  | `(`[LC| $x:ident]) => `(LambdaCalc.var $(Lean.Syntax.mkStrLit x.getId.toString))
  | `(`[LC| ( $e:LambdaCalcSyntax )]) => `(`[LC| $e])
  | `(`[LC| λ $x:ident . $body:LambdaCalcSyntax]) => `(LambdaCalc.lam
$(Lean.Syntax.mkStrLit x.getId.toString) `[LC| $body])
  | `(`[LC| @ $e₁:LambdaCalcSyntax $e₂:LambdaCalcSyntax]) => `(LambdaCalc.app `[LC|
$e₁] `[LC| $e₂])
  | `(`[LC| $e₁:LambdaCalcSyntax + $e₂:LambdaCalcSyntax]) => `(LambdaCalc.appPrim .add `[LC| $e₁] `[LC| $e₂])
  | `(`[LC| $e₁:LambdaCalcSyntax - $e₂:LambdaCalcSyntax]) => `(LambdaCalc.appPrim .sub `[LC| $e₁] `[LC| $e₂])
  | `(`[LC| $e₁:LambdaCalcSyntax * $e₂:LambdaCalcSyntax]) => `(LambdaCalc.appPrim .mul `[LC| $e₁] `[LC| $e₂])
  | `(`[LC| $e₁:LambdaCalcSyntax / $e₂:LambdaCalcSyntax]) => `(LambdaCalc.appPrim .div `[LC| $e₁] `[LC| $e₂])
  | `(`[LC| $e₁:LambdaCalcSyntax == $e₂:LambdaCalcSyntax]) => `(LambdaCalc.appPrim .eq `[LC| $e₁] `[LC| $e₂])
  | `(`[LC| let [ $x:ident $e₁:LambdaCalcSyntax ] $e₂:LambdaCalcSyntax]) =>
      `(LambdaCalc.letIn $(Lean.Syntax.mkStrLit x.getId.toString) `[LC| $e₁] `[LC|
$e₂])
      -- Above let can be changed to use λ and @ only, if desired.
      -- `(LambdaCalc.app (LambdaCalc.lam $(Lean.Syntax.mkStrLit x.getId.toString) `[LC| $e₂]) `[LC| $e₁])
/-- Example expressions matching assignment specification. -/

def ex1 := `[LC| 42]
def ex2 := `[LC| x]
def ex3 := `[LC| 1 + 2 * 3 - 10 / 5]
def ex4 := `[LC| λ x. x + 1]
def ex5 := `[LC| @ (λ x. x + 1) 5]
def ex6 := `[LC| let [ x 5 ] x + 3]
def ex7 := `[LC| @ (@ (λ x. λ y. x + y) 3) 4]
#eval evalPP ex1
#eval evalPP ex2
#eval eval [("x", .num 10)] ex2
#eval evalPP ex3
#eval evalPP ex5
#eval evalPP ex6
#eval evalPP ex7
#eval toString ex1
#eval toString ex2
#eval toString ex3
#eval toString ex4
#eval toString ex5
#eval toString ex6
#eval toString ex7
