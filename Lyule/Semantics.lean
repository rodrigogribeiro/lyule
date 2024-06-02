import Mathlib.Data.Finmap 
import Mathlib.Data.Nat.Defs

import Lyule.Syntax

-- definition of values 

inductive Val : Type where
| VNat : ℕ → Val
| VBool : Bool → Val 
| VUnit : Val 
| VPair : Val → Val → Val 
| VInl : Val → Val 
| VInr : Val → Val 
deriving Repr

open Val Ty 

def Ty.defaultVal : Ty → Val 
| TNat => VNat 0 
| TBool => VBool false 
| TUnit => VUnit 
| TPair t1 t2 => VPair t1.defaultVal t2.defaultVal
| TSum t1 _ => VInl t1.defaultVal 
| TFun _ tr => tr.defaultVal

abbrev VarEnv := Finmap (λ _ : Name => Val)
abbrev FunEnv := Finmap (λ _ : Name => Function)

inductive Status where 
| Ok : Status
| OutOfGas : Status
| VarNotFound : Name → Status
| UndefinedFunction : Name → Status
| InvalidOperation : Status  
| UnknownError : Status

structure State (A : Type) where 
  result : A 
  varenv : VarEnv 
  funenv : FunEnv 
  status : Status 

open Expr State Status Stmt  

def State.setResult {A : Type}(s : State A)(v : A) : State A := 
  match s.status with 
  | .Ok => State.mk v s.varenv s.funenv .Ok
  | _   => s

def State.setStatus {A : Type}(s : State A)(s' : Status) : State A := 
  match s.status with 
  | .Ok => State.mk s.result s.varenv s.funenv s'
  | _ => s 

def State.first (s : State Val) : State Val := 
  match s.result with 
  | VPair v1 _ => s.setResult v1
  | _ => s.setStatus InvalidOperation

def State.second (s : State Val) : State Val := 
  match s.result with 
  | VPair _ v2 => s.setResult v2
  | _ => s.setStatus InvalidOperation

def State.insert (s : State Val)(n : Name)(v : Val) : State Val := 
  State.mk s.result (s.varenv.insert n v) s.funenv s.status

def State.remove (s : State Val)(n : Name) : State Val :=
  State.mk s.result (s.varenv.erase n) s.funenv s.status 

def insertMany : List (Name × Val) → State Val → State Val 
| defs , s => defs.foldr (λ p ac => ac.insert p.1 p.2) s

def removeMany : List Name → State Val → State Val 
| defs , s => defs.foldr (λ n ac => ac.remove n) s 

mutual 

  def evalVar (v : Name)(s : State Val) : State Val := 
    match Finmap.lookup v s.varenv with 
    | .some val => s.setResult val
    | .none => s.setStatus (.VarNotFound v)

  def evalCall (fuel : ℕ)(f : Name)
               (args : List Expr)(s : State Val) : State Val := 
    match fuel with 
    | 0 => s.setStatus .OutOfGas
    | fuel' + 1 => 
      match Finmap.lookup f s.funenv with 
      | .some fd => 
        let vals := args.map (λ e => (evalExp fuel' e s).result)
        let argNames := fd.parameters.map (λ (n, _) => n)
        let newEnv := argNames.zip vals 
        let s1 := evalBlock fuel' fd.body (insertMany newEnv s) 
        removeMany argNames s1
      | .none => s.setStatus (.UndefinedFunction f)
    
  def evalExp (fuel : ℕ)(e : Expr)(s : State Val) : State Val := 
    match fuel with 
    | 0 => s.setStatus .OutOfGas 
    | fuel' + 1 => 
       match e with 
       | ENat n => s.setResult (VNat n)  
       | EBool b => s.setResult (VBool b)
       | EUnit => s.setResult VUnit
       | EVar v => evalVar v s 
       | EPair e1 e2 => 
          let s1 := evalExp fuel' e1 s
          let s2 := evalExp fuel' e2 s1 
          s2.setResult (VPair s1.result s2.result)
       | EFst e1 => 
          let s1 := evalExp fuel' e1 s
          s1.first 
       | ESnd e1 => 
          let s1 := evalExp fuel' e1 s
          s1.second
       | EInl e1 =>
          let s1 := evalExp fuel' e1 s 
          s1.setResult (VInl s1.result)
       | EInr e1 => 
          let s1 := evalExp fuel' e1 s 
          s1.setResult (VInr s1.result)
       | ECall n es => evalCall fuel' n es s

  def evalBlock (fuel : ℕ)(blk : List Stmt)(s : State Val) : State Val :=
    match fuel with 
    | 0 => s.setStatus .OutOfGas
    | fuel' + 1 => 
      match blk with 
      | [] => s 
      | (s1 :: ss') => 
        evalBlock fuel' ss' (evalStmt fuel' s1 s)

  def evalStmt (fuel : ℕ)(e : Stmt)(s : State Val) : State Val := 
    match fuel with 
    | 0 => s.setStatus .OutOfGas
    | fuel' + 1 => 
      match e with 
      | SAssign n e1 => 
        let s1 := evalExp fuel' e1 s 
        s1.insert n s1.result 
      | SAlloc n t => 
        s.insert n t.defaultVal
      | SExpr e => 
        evalExp fuel' e s 
      | SReturn e => 
        let s1 := evalExp fuel' e s 
        s1 -- fix status here 
      | SBlock blk => evalBlock fuel' blk s 
      | SCase e _eqns => evalExp fuel' e s 
end 
