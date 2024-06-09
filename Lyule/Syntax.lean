import Mathlib.Data.Nat.Defs
import Lyule.Utils

-- type syntax

inductive Ty : Type where 
| TNat : Ty 
| TBool : Ty 
| TUnit : Ty 
| TPair : Ty → Ty → Ty 
| TSum : Ty → Ty → Ty 
deriving Repr 

-- typing environments

abbrev Ctx := List Ty 

-- function signatures 

structure Sig : Type where 
  params : List Ty 
  ret : Ty 
deriving Repr 

-- function signature environments

abbrev FCtx := List Sig 

open Ty

mutual

  -- function call arguments 

  inductive Args (fctx : FCtx) : Ctx → List Ty → Type where 
  | Nil : ∀ {ctx}, Args fctx ctx []
  | Cons : ∀ {ctx t ts}, Expr fctx ctx t → 
                         Args fctx ctx ts → 
                         Args fctx ctx (t :: ts)
  deriving Repr

  -- expressions 

  inductive Expr (fctx : FCtx) : Ctx → Ty → Type where 
  | EBool : ∀ {ctx}, Bool → 
                     Expr fctx ctx TBool 
  | ENat : ∀ {ctx}, ℕ → 
                    Expr fctx ctx TNat 
  | EUnit : Expr fctx ctx TUnit 
  | EVar : ∀ {ctx t}, Idx t ctx → 
                      Expr fctx ctx t 
  | EInl : ∀ {t ctx}(t' : Ty), 
                    Expr fctx ctx t → 
                    Expr fctx ctx (TSum t t')
  | EInr : ∀ (t : Ty){ctx t'}, 
                      Expr fctx ctx t' → 
                      Expr fctx ctx (TSum t t')
  | EPair : ∀ {t t' ctx}, 
                      Expr fctx ctx t → 
                      Expr fctx ctx t' → 
                      Expr fctx ctx (TPair t t')
  | EFst : ∀ {t t' ctx},
                      Expr fctx ctx (TPair t t') → 
                      Expr fctx ctx t 
  | ESnd : ∀ {t t' ctx},
                      Expr fctx ctx (TPair t t') → 
                      Expr fctx ctx t' 
  | ECall : ∀ {s ctx}, 
              Idx s fctx → 
              Args fctx ctx s.params → 
              Expr fctx ctx s.ret
          
  deriving Repr 

  -- statements 

  inductive Stmt (fctx : FCtx) : Ctx → Ctx → Type where 
  | SDecl : ∀ {ctx t}, Expr fctx ctx t → 
                  Stmt fctx ctx (t :: ctx)
  | SAssign : ∀ {ctx t}, Idx t ctx → 
                    Expr fctx ctx t → 
                    Stmt fctx ctx ctx
  | SExpr : ∀ {ctx t}, Expr fctx ctx t → Stmt fctx ctx ctx 
  | SCase : ∀ {ctx ctx' t t'}, 
              Expr fctx ctx (TSum t t') → 
              Block fctx (t :: ctx) ctx' → 
              Block fctx (t' :: ctx) ctx' → 
              Stmt fctx ctx ctx'
  deriving Repr 

  -- functions 

  inductive Block (fctx : FCtx) : Ctx → Ctx → Type where 
  | Done : ∀ {ctx}, Block fctx ctx ctx 
  | Next : ∀ {ctx ctx1 ctx'}, 
                Stmt fctx ctx ctx1 → 
                Block fctx ctx1 ctx' → 
                Block fctx ctx ctx'
  deriving Repr

  inductive Func (fctx : FCtx) : Sig → Type where 
  | MkFunc : ∀ {ctx}(c : Sig), 
              Block fctx c.params ctx →
              Expr fctx ctx c.ret → 
              Func fctx c
  deriving Repr
end 

abbrev Functions fctx := All (Func fctx) fctx

-- complete programs 

inductive Program : Type where 
| MkProg {fctx ctx} : Functions fctx → Block fctx [] ctx → Program
