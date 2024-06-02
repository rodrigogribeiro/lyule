import Mathlib.Data.Finmap
import Mathlib.Data.Nat.Defs 

-- definition of the type syntax 

inductive Ty : Type where 
| TNat : Ty 
| TBool : Ty 
| TUnit : Ty 
| TPair : Ty → Ty → Ty 
| TSum : Ty → Ty → Ty 
| TFun : List Ty → Ty → Ty  
deriving Repr 

-- definition of the expresson syntax 

abbrev Name := ℕ 

inductive Expr : Type where 
| ENat : ℕ → Expr 
| EBool : Bool → Expr 
| EUnit : Expr
| EVar : Name → Expr 
| EPair : Expr → Expr → Expr 
| EFst : Expr → Expr 
| ESnd : Expr → Expr 
| EInl : Expr → Expr 
| EInr : Expr → Expr 
| ECall : Name → List Expr → Expr
deriving Repr

-- definition of the statement syntax 

inductive Stmt : Type where 
| SAssign : Name → Expr → Stmt 
| SAlloc : Name → Ty → Stmt 
| SExpr : Expr → Stmt 
| SReturn : Expr → Stmt 
| SBlock : List Stmt → Stmt 
| SCase : Expr → List (Name × List Stmt) → Stmt 
deriving Repr

-- top level definitions 

structure Function : Type where 
  name : Name 
  parameters : List (Name × Ty)
  returnType : Ty 
  body : List Stmt
deriving Repr 

-- programs 

structure Prog : Type where
  functions : Finmap (λ _ : Name => Function)
  mainBody : List Stmt 
