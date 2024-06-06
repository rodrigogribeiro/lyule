import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Defs


-- Typed De Bruijn indexes infra 

section DEBRUIJN
  variable {A : Type}

  inductive Idx (x : A) : List A → Type where 
  | Here : ∀ {xs}, Idx x (x :: xs)
  | There : ∀ {y ys}, Idx x ys → Idx x (y :: ys)
  deriving Repr 

end DEBRUIJN

-- type level all predicate 

section ALL 

  inductive All {A}(P : A → Type) : List A → Type where 
  | Nil : All P []
  | Cons : ∀ {x xs}, P x → All P xs → All P (x :: xs)

  def lookup {P xs}{x : A} : All P xs → Idx x xs → P x 
  | All.Cons px _, Idx.Here => px 
  | All.Cons _ xs, (Idx.There idx) => lookup xs idx
end ALL 

-- type syntax 

inductive Ty : Type where 
| TNat : Ty 
| TBool : Ty 
| TUnit : Ty 
| TPair : Ty → Ty → Ty 
| TSum : Ty → Ty → Ty 
deriving Repr 

abbrev Ctx := List Ty 

open Ty 

-- interpreting types 

def Ty.asType : Ty → Type 
| TNat => ℕ 
| TBool => Bool 
| TUnit => Unit 
| TPair t1 t2 => t1.asType × t2.asType
| TSum t1 t2 => t1.asType ⊕ t2.asType 

-- function signatures 

structure Sig : Type where 
  params : List Ty 
  ret : Ty 
deriving Repr 

abbrev FCtx := List Sig 

mutual

  inductive Args : FCtx → Ctx → List Ty → Type where 
  | Nil : ∀ {fctx ctx}, Args fctx ctx []
  | Cons : ∀ {fctx ctx t ts}, Expr fctx ctx t → 
                              Args fctx ctx ts → 
                              Args fctx ctx (t :: ts)
  deriving Repr

  -- expressions 

  inductive Expr : FCtx → Ctx → Ty → Type where 
  | EBool : ∀ {fctx ctx}, Bool → 
                          Expr fctx ctx TBool 
  | ENat : ∀ {fctx ctx}, ℕ → 
                         Expr fctx ctx TNat 
  | EUnit : ∀ {fctx ctx}, Expr fctx ctx TUnit 
  | EVar : ∀ {fctx ctx t}, Idx t ctx → 
                           Expr fctx ctx t 
  | EInl : ∀ {t fctx ctx}(t' : Ty), 
                         Expr fctx ctx t → 
                         Expr fctx ctx (TSum t t')
  | EInr : ∀ (t : Ty){fctx ctx t'}, 
                      Expr fctx ctx t' → 
                      Expr fctx ctx (TSum t t')
  | EPair : ∀ {t t' fctx ctx}, 
                      Expr fctx ctx t → 
                      Expr fctx ctx t' → 
                      Expr fctx ctx (TPair t t')
  | ECall : ∀ {s fctx ctx}, 
              Idx s fctx → 
              Args fctx ctx s.params → 
              Expr fctx ctx s.ret
          
  deriving Repr 

  -- statements 

  inductive Stmt : FCtx → Ctx → Ctx → Type where 
  | Decl : ∀ {fctx ctx t}, Expr fctx ctx t → 
                  Stmt fctx ctx (t :: ctx)
  | Assign : ∀ {fctx ctx t}, Idx t ctx → 
                    Expr fctx ctx t → 
                    Stmt fctx ctx ctx
  deriving Repr 

  -- functions 

  inductive Block : FCtx → Ctx → Ctx → Type where 
  | Done : ∀ {fctx ctx}, Block fctx ctx ctx 
  | Next : ∀ {ctx ctx1 ctx'}, 
                Stmt fctx ctx ctx1 → 
                Block fctx ctx1 ctx' → 
                Block fctx ctx ctx'
  deriving Repr

  inductive Func : FCtx → Sig → Type where 
  | MkFunc : ∀ {fctx ctx}(c : Sig), 
              Block fctx c.params ctx → 
              Func fctx c
  deriving Repr

  inductive Functions : FCtx → Type where 
  | Nil : Functions []
  | Cons : ∀ {fctx s}, Func fctx s → 
                       Functions fctx →
                       Functions (s :: fctx)

  inductive Program : Type where 
  | MkProg {fctx ctx} : Functions fctx → Block fctx [] ctx → Program

end 
