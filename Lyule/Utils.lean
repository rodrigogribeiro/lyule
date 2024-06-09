-- typed De Bruijn indexes. 

inductive Idx {A : Type}(x : A) : List A → Type where 
| Here : ∀ {xs}, Idx x (x :: xs)
| There : ∀ {y ys}, Idx x ys → Idx x (y :: ys)
deriving Repr 

-- type level all predicate

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


