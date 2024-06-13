import Mathlib.Data.Nat.Defs
import Lyule.Utils
import Lyule.Syntax

open Ty 

-- interpreting types 

def Ty.asType : Ty → Type 
| TNat => ℕ 
| TBool => Bool 
| TUnit => Unit 
| TPair t1 t2 => t1.asType × t2.asType
| TSum t1 t2 => t1.asType ⊕ t2.asType 

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

-- All P xs ↔ ∀ {x}, x ∈ xs → P x

def lookupVar {ctx t} : Idx t ctx → Env ctx → Val t
| idx, env => lookupAll env idx

-- definitional interpreter 

abbrev Fuel := ℕ 

mutual
  
  def evalExp {ctx fctx t}
      : Fuel → Expr fctx ctx t → 
               Functions fctx → 
               Env ctx → Result (Val t) 
  | 0, _ , _, _ => .Timeout 
  | _, Expr.ENat n, _, _ => pure (Val.VNat n)
  | _, Expr.EBool b, _, _ => pure (Val.VBool b)
  | _, Expr.EUnit, _, _ => pure Val.VUnit 
  | _, Expr.EVar v, _, env => pure (lookupVar v env)
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
                          Result (Val s.ret)
  | 0, _, _, _ => .Timeout 
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
                               Result (Env ps)
  | 0, _, _, _ => .Timeout 
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
                                 Result (Env ctx') 
  | 0, _, _, _ => .Timeout
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
                                      Result (Env ctx')
  | 0, _ ,_ ,_ , _, _ => .Timeout 
  | fuel' + 1, Val.VInl _ v, bl, _, fenv, env => 
     evalBlock fuel' bl fenv (All.Cons v env)
  | fuel' + 1, Val.VInr _ v, _, br, fenv, env =>
    evalBlock fuel' br fenv (All.Cons v env)
  termination_by fuel' => fuel' 

  def evalBlock {fctx ctx ctx'} : Fuel → 
                                  Block fctx ctx ctx' → 
                                  Functions fctx → 
                                  Env ctx → 
                                  Result (Env ctx') 
  | 0, _, _, _ => .Timeout 
  | _fuel' + 1, Block.Done , _, env => pure env
  | fuel' + 1, Block.Next s blk, fenv, env => 
    do 
      let env1 ← evalStmt fuel' s fenv env 
      evalBlock fuel' blk fenv env1
  termination_by fuel' => fuel'
end 

-- full program evaluation

def evalProg : Fuel → Program → Result (Σ ctx : Ctx , Env ctx)
| fuel, (Program.MkProg fs blk) => 
  do 
    let env1 ← evalBlock fuel blk fs All.Nil 
    pure (Sigma.mk _ env1)
