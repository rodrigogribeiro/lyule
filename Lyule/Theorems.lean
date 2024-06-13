import Lyule.Semantics 
import Lyule.Syntax 
import Lyule.Utils

import Aesop 

-- Lemma 2 of Amin and Rompf paper. 
-- lemma: well-typed lookups are not stuck and preserves types 
-- This proof is immediate because this property is ensured by 
-- construction for the function lookupVar. 

lemma lookupVarLemma {ctx t} 
  : ∀ (env : Env ctx)(p : Idx t ctx), ∃ v : Val t, lookupVar p env = v := by 
  intros env p 
  exists (lookupVar p env)

-- well typed lookup lemma for functions 

lemma lookupFunLemma {fctx s} 
  : ∀ (fenv : Functions fctx)(p : Idx s fctx), ∃ f : Func fctx s, 
      lookupAll fenv p = f := by 
    intros fenv p
    exists (lookupAll fenv p) 

-- Lemma 3 of Amin and Rompf paper 

lemma evalLemma 
  : ∀ (n : Fuel)(prog : Program)(p : Σ ctx, Env ctx),  
      evalProg n prog = .Ok p → 
      ∃ (ctx : Ctx)(env : Env ctx), p = Sigma.mk _ env := by
      intros n 
      induction n with 
      | zero => 
        intros _prog p 
        simp [evalProg] 
        aesop  
      | succ n' _IH => 
        intros _prog p _H 
        exists p.1
        exists p.2

-- type soundness lemma 

theorem soundness 
  : ∀ n prog p, evalProg n prog = p → (∃ (ctx : Ctx)(env : Env ctx), p = .Ok (Sigma.mk ctx env)) ∨ 
                                      p = .Timeout := by 
      intros n prog p H 
      rcases p with ⟨ ctx , env ⟩ | _ 
      · 
        left 
        exists ctx 
        exists env 
      · 
        right 
        rfl  

