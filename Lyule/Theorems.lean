import Lyule.Semantics 
import Lyule.Syntax 
import Lyule.Utils

-- Lemma 2 of Amin and Rompf paper. 
-- lemma: well-typed lookups are not stuck and preserves types 
-- This proof is immediate because this property is ensured by 
-- construction for the function lookupVar. 

lemma lookupVarLemma {ctx t} 
  : ∀ (env : Env ctx)(p : Idx t ctx), ∃ v : Val t, lookupVar p env = v := by 
  intros env p 
  exists (lookupVar p env)

lemma lookupFunLemma {fctx s} 
  : ∀ (fenv : Functions fctx)(p : Idx s fctx), ∃ f : Func fctx s, 
      lookupAll fenv p = f := by 
    intros fenv p
    exists (lookupAll fenv p) 

