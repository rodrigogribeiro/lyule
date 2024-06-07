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

inductive All {A : Type}
              (P : A → Type) : List A → Type where 
| Nil : All P []
| Cons : ∀ {x xs}, P x → All P xs → All P (x :: xs)

def lookupAll {A : Type}
              {x xs}
              {P : A → Type}
              : All P xs → Idx x xs → P x 
| All.Cons px _, Idx.Here => px 
| All.Cons _ pxs, Idx.There idx => lookupAll pxs idx

def updateAll {A : Type}
              {x xs}
              {P : A → Type}
              : All P xs → Idx x xs → P x → All P xs 
| All.Cons _ pxs, Idx.Here, px => All.Cons px pxs 
| All.Cons px pxs, Idx.There idx, px' => 
  All.Cons px (updateAll pxs idx px') 

abbrev Functions fctx := All (Func fctx) fctx

-- definition of values 

inductive Val : Ty → Type where 
| VNat : ℕ → Val TNat
| VBool : Bool → Val TBool 
| VUnit : Val TUnit 
| VInl : ∀ {t}(t' : Ty), 
              Val t → 
              Val (TSum t t')
| VInr : ∀ {t'}(t : Ty), 
               Val t' → 
               Val (TSum t t')
| VPair : ∀ {t t'}, 
               Val t → 
               Val t' → 
               Val (TPair t t')
deriving Repr 

def vfst {t t'} : Val (TPair t t') → Val t 
| Val.VPair v1 _ => v1 

def vsnd {t t'} : Val (TPair t t') → Val t'
| Val.VPair _ v2 => v2

--definition of value environment 

abbrev Env ctx := All Val ctx 

def lookupVar {ctx t} : Idx t ctx → Env ctx → Val t
| idx, env => lookupAll env idx

-- definitional interpreter 

abbrev Fuel := ℕ 

mutual
  
  def evalExp {ctx fctx t}
      : Fuel → Expr fctx ctx t → 
               Functions fctx → 
               Env ctx → Option (Val t) 
  | 0, _ , _, _ => .none 
  | _, Expr.ENat n, _, _ => pure (Val.VNat n)
  | _, Expr.EBool b, _, _ => pure (Val.VBool b)
  | _, Expr.EUnit, _, _ => pure Val.VUnit 
  | _, Expr.EVar v, _, env => lookupVar v env
  | fuel' + 1, Expr.EInl t e, fenv, env => 
    do
      let v1 ← evalExp fuel' e fenv env 
      pure (Val.VInl t v1)
  | fuel' + 1, Expr.EInr t e, fenv, env => 
    do
      let v1 ← evalExp fuel' e fenv env 
      pure (Val.VInr t v1)
  | fuel' + 1, Expr.EPair e1 e2, fenv, env => 
    do 
      let v1 ← evalExp fuel' e1 fenv env 
      let v2 ← evalExp fuel' e2 fenv env 
      pure (Val.VPair v1 v2)
  | fuel' + 1, Expr.EFst e, fenv, env => 
    do 
      let v1 ← evalExp fuel' e fenv env 
      pure (vfst v1)
  | fuel' + 1, Expr.ESnd e, fenv, env => 
    do 
      let v1 ← evalExp fuel' e fenv env 
      pure (vsnd v1)
  | fuel' + 1, Expr.ECall idx args, fenv, env => 
    do 
      let vals ← evalArgs fuel' args fenv env
      evalCall fuel' (lookupAll fenv idx) fenv vals  
  termination_by fuel' => fuel'

  def evalCall {fctx s} : Fuel → 
                          Func fctx s → 
                          Functions fctx → 
                          Env s.params → 
                          Option (Val s.ret)
  | 0, _, _, _ => .none 
  | fuel' + 1, Func.MkFunc s bd e, fenv, env => 
    do 
      let env1 ← evalBlock fuel' bd fenv env 
      let env' ← evalExp fuel' e fenv env1 
      pure env'
  termination_by fuel' => fuel'

  def evalArgs {fctx ctx ps} : Fuel → 
                               Args fctx ctx ps → 
                               Functions fctx → 
                               Env ctx → 
                               Option (Env ps)
  | 0, _, _, _ => .none 
  | _fuel' + 1, Args.Nil, _ , _ => pure All.Nil
  | fuel' + 1, Args.Cons arg args, fenv, env => 
    do 
      let v ← evalExp fuel' arg fenv env 
      let vs ← evalArgs fuel' args fenv env 
      pure (All.Cons v vs)
  termination_by fuel' => fuel'


  def evalStmt {fctx ctx ctx'} : Fuel → 
                                 Stmt fctx ctx ctx' → 
                                 Functions fctx → 
                                 Env ctx → 
                                 Option (Env ctx') 
  | 0, _, _, _ => .none
  | fuel' + 1, Stmt.SDecl e , fenv, env => 
    do 
      let v1 ← evalExp fuel' e fenv env 
      pure (All.Cons v1 env)
  | fuel' + 1, Stmt.SAssign idx e, fenv, env => 
    do 
      let v1 ← evalExp fuel' e fenv env 
      pure (updateAll env idx v1)
  | fuel' + 1, Stmt.SExpr e, fenv, env => 
      do 
        let _v1 ← evalExp fuel' e fenv env 
        pure env
  | fuel' + 1, Stmt.SCase e bl br, fenv, env => 
    do 
      let v ← evalExp fuel' e fenv env
      let env' ← evalCase fuel' v bl br fenv env
      pure env'
  termination_by fuel' => fuel' 

  def evalCase {fctx ctx ctx' t t'} : Fuel → 
                                      Val (TSum t t') → 
                                      Block fctx (t :: ctx) ctx' → 
                                      Block fctx (t' :: ctx) ctx' → 
                                      Functions fctx → 
                                      Env ctx → 
                                      Option (Env ctx')
  | 0, _ ,_ ,_ , _, _ => .none 
  | fuel' + 1, Val.VInl _ v, bl, _, fenv, env => 
     evalBlock fuel' bl fenv (All.Cons v env)
  | fuel' + 1, Val.VInr _ v, _, br, fenv, env =>
    evalBlock fuel' br fenv (All.Cons v env)
  termination_by fuel' => fuel' 

  def evalBlock {fctx ctx ctx'} : Fuel → 
                                  Block fctx ctx ctx' → 
                                  Functions fctx → 
                                  Env ctx → 
                                  Option (Env ctx') 
  | 0, _, _, _ => .none 
  | _fuel' + 1, Block.Done , _, env => pure env
  | fuel' + 1, Block.Next s blk, fenv, env => 
    do 
      let env1 ← evalStmt fuel' s fenv env 
      evalBlock fuel' blk fenv env1
  termination_by fuel' => fuel'
end 

-- evaluation of complete programs

inductive Program : Type where 
| MkProg {fctx ctx} : Functions fctx → Block fctx [] ctx → Program

def evalProg : Fuel → Program → Option (Σ ctx : Ctx , Env ctx)
| 0, _ => .none 
| fuel' + 1, (Program.MkProg fs blk) => 
  do 
    let env1 ← evalBlock fuel' blk fs All.Nil 
    pure (Sigma.mk _ env1)
