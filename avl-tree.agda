
open import bool
open import bool-thms
open import bool-thms2
open import eq
open import list
open import nat
open import nat-thms
open import maybe
open import product
open import product-thms
open import sum
open import relations using (transitive; total)

module treebal (A : Set) (_≤A_ : A → A → 𝔹)
           (≤A-trans : transitive A _≤A_)
           (≤A-total : total A _≤A_) where


{-attempted abstraction to Set A
data balance : A → A → A → Set  where
     less : ∀ {a b : A} → a → b → (a ≤A b ≡ tt) && (b ≤ a ≡ ff)  → balance b
     same-left :  ∀ {a b : A} → a  → b → (a ≤A b ≡ tt) && (b ≤ a ≡ tt) → balance a 
     same-right :  ∀ {a b : A} → a  → b → (a ≤A b ≡ tt) && (b ≤ a ≡ tt) → balance b 
     more : ∀ {a b : A} → a → b → (b ≤A a ≡ tt) && (a ≤ b ≡ ff)  → balance a
-}

data avl :  ℕ → maybe A → A → A → Set where
     avl-leaf : ∀ {l u : A} → l ≤A u ≡ tt → avl 0 nothing l u
     avl-node : ∀ {n m : ℕ}{k l u v : A}{p q : maybe A}(d : A) → 
           avl n p k u  → avl m q l v →
           n ≡ m ∨ n ≡ suc m ∨ m ≡ suc n →
           u ≤A d ≡ tt → d ≤A k ≡ tt →
           avl (suc(max m n)) (just d) l u --(avl p k u) (avl q l v)
{-
--Serves the same function as: n ≡ m ∨ n ≡ suc m ∨ m ≡ suc n 
data bal : ℕ → ℕ → ℕ → Set  where
     less : ∀ {n : ℕ} n → (suc n) → bal (suc n)
     same :  ∀ {n : ℕ} → n → n → bal n
     more :  ∀ {n : ℕ} → (suc n) →  n → bal (suc n)


data avl* : {- ℕ → -}maybe A → A → A → Set where
     avl*-leaf : ∀ {l u : A} → l ≤A u ≡ tt → avl* nothing l u
     avl*-node : ∀ {-n m : ℕ-}{k l u v : A}{p q : maybe A}(d : A) → 
           avl* p k u  → avl* q l v →
           --n ≡ m ∨ n ≡ suc m ∨ m ≡ suc n →
           u ≤A d ≡ tt → d ≤A k ≡ tt →
           avl* {-(suc(max m n))-} (just d) l u --(avl* p k u) (avl* q l v)

-}


--Half of the holes are from a problem that I have with defining the new avl trees. I guess I have a problem with the hidden arguments; they want me to pass .m or .k, but I pass something with the same type as .m,k, etc. So that's throwing me for a loop
--the other holes I would be able to get if i could just move past the hidden argument problem

depth : ∀ {l u : A} {n : ℕ} {p : maybe A} → avl n p l u → ℕ
depth (avl-leaf x) = 0
depth (avl-node d n₁ n₂ x x₁ x₂) =  (max (depth n₁) (depth n₂)) + 1


inorder :  ∀ {l u : A} {n : ℕ}{p : maybe A} → avl n p l u → 𝕃 A
inorder (avl-leaf x) = [] 
inorder (avl-node d n₁ n₂ x x₁ x₂) = inorder n₁ ++ [ d ] ++ inorder n₂


--try explicitly defining the solution as the appropriate subtree
--these are the same as the bst dec-lb and bst inc-ub functions
left-avl :  ∀ {l k v u : A}{n m : ℕ} {p q : maybe A} → avl n p l u  →  avl (pred n) q k v
left-avl  (avl-leaf x)  = {!avl-leaf x!}
left-avl (avl-node d l u x y z)  = {!l!}

right-avl :   ∀ {l k v u : A}{n m : ℕ}{p q : maybe A} →  avl n p l u →  avl m q k v
right-avl (avl-leaf x) = {!avl-leaf x!}
right-avl (avl-node d l u x x₁ x₂) = {!u!}

value-avl :   ∀ {l k v u : A}{n m : ℕ}{p q : maybe A} →  avl n p l u → maybe A 
value-avl (avl-leaf x) = nothing 
value-avl (avl-node d v₂ v₃ x y z) = just d 

avl-pivot :  ∀ {l u : A} {n : ℕ} {p : maybe A} → avl n p l u → maybe A
avl-pivot (avl-leaf x)  = nothing
avl-pivot (avl-node d l r x y z) = just d

avl-min : ∀ {l u : A} {n : ℕ} {p : maybe A} → avl n p l u → maybe A
avl-min (avl-leaf x) = nothing 
avl-min (avl-node d (avl-leaf x) p₂ x₁ x₂ x₃) = just d
avl-min (avl-node d (avl-node b q q₁ u v w) p₃ x₃ x₄ x₅) = avl-min  (avl-node b q q₁ u v w) 

avl-max :  ∀ {l u : A} {n : ℕ} {p : maybe A} → avl n p l u → maybe A
avl-max (avl-leaf x) = nothing 
avl-max (avl-node d n₁ (avl-leaf x) x₁ x₂ x₃) = just d 
avl-max (avl-node d n₁ (avl-node d₁ n₃ n₄ x x₁ x₂) x₃ x₄ x₅) = avl-max  (avl-node d₁ n₃ n₄ x x₁ x₂)


balFactor : ∀ {l k v u : A} {n m : ℕ} {p q : maybe A} → avl n p l u  → avl m q k v → ℕ
balFactor t u = (depth t) ∸ (depth u)

search : ∀ {l u : A} {n : ℕ} {p : maybe A} → avl n p l u → A → 𝔹 
search (avl-leaf x) a = ff 
search (avl-node d n₁ n₂ x x₁ x₂) a with (a ≤A d)
search (avl-node d n₁ n₂ x x₁ x₂) a | tt = tt 
search (avl-node d l u x x₁ x₂) a | ff = (search l a ) || (search u a) 


balanceLL :  ∀ {l k v u : A} → ∀ {n m : ℕ} → ∀ {p q : maybe A} →  avl n p l u → avl m q k v
balanceLL (avl-leaf  p ) = {!avl-leaf p!} 
balanceLL (avl-node d (avl-leaf w) (avl-leaf x) x₁ y z) = {! (avl-node d (avl-leaf w) (avl-leaf x) x₁ y z)!}
balanceLL (avl-node d (avl-leaf w) (avl-node d₁ l r x x₁ x₂) s y z) = {!avl-node d₁ (insert l d) r x x₁ x₂!}
balanceLL (avl-node d (avl-node b l r v w₁ w₂) u x y z) = {!!} 
--balanceLL (avl-node N v (avl-node M vl tl ul) R)  = (avl-node N vl tl (avl-node M v ul u))

balanceLR :  ∀ {l k v u : A}{n m : ℕ}{p q : maybe A} →  avl n p l u → avl m q k v
balanceLR (avl-leaf x) = {!avl-leaf x!}
balanceLR (avl-node d n₁ n₂ x x₁ x₂) = {!!}
--balanceLR (avl-node N v (avl-node M vl tl (avl-node P vlr tlr ulr)) u) = (avl-node N vlr (avl-node M vl tl tlr) (avl-node P v ulr u))

balanceRL :  ∀ {l k v u : A}{n m : ℕ}{p q : maybe A} →  avl n p l u → avl m q k v
balanceRL (avl-leaf x) = {!avl-leaf x!}
balanceRL (avl-node d n₁ n₂ x x₁ x₂) = {!!}
--balanceRL (avl-node N v t (avl-node M vr (avl-node P vrl trl url) ur)) = (avl-node N vrl (avl-node M v t trl) (avl-node P vr url ur))

balanceRR  :  ∀ {l k v u : A}{n m : ℕ}{p q : maybe A} →  avl n p l u → avl m q k v
balanceRR (avl-leaf x) = {!avl-leaf x!}
balanceRR (avl-node d n₁ n₂ x x₁ x₂) = {!!}
--balanceRR (avl-node N v t (avl-node M vr tr ur)) = (avl-node N vr (avl-node M v t tr) ur)

{- Balanced insert -}

insert :  ∀ {l k v u : A}{n m : ℕ}{p q : maybe A} →  avl n p l u → A → avl m q k v
insert (avl-leaf x) a = {!avl-node a (avl-leaf x) (avl-leaf x)!}
insert (avl-node d n₁ n₂ x x₁ x₂) a = {!!} --L i = (avl-node 1 i L L)
{-insert (avl-node N v t u) i with i ≡ v
...| tt = (avl-node N v t u)
...| ff rewrite (( i < v ) && ((balFactor (insert t i) u) ≡  ( 2 && (i < value-avl t) ))) =  balanceLL (avl-node N v insert t i u)
...| ff rewrite (( i < v ) && ((balFactor (insert t i) u) ≡ ( 2 && (value-avl t < i) ))) = balanceLR (avl-node N v insert t i u)
...| ff rewrite (( v < i ) && ((balFactor t (insert u i)) ≡ ( ff && (i < value-avl u) ))) = balanceRL (avl-node N v t (insert u i))
...| ff rewrite (( v < i ) && ((balFactor t (insert u i)) ≡ ( ff && (value-avl u < i) ))) = balanceRR (avl-node N v t (insert u i))
...| ff rewrite ( i < v ) = (avl-node N v (insert t i) u)
...| ff rewrite ( v < i ) = (avl-node N v t (insert u i))
-}


{- Balanced delete -}
delete :  ∀ {l k v u : A}{n m : ℕ}{p q : maybe A} →  avl n p l u → A → avl m q k v
delete (avl-leaf x) a = {!avl-leaf x!}
delete (avl-node d n₁ n₂ x x₁ x₂) a = {!!} --0 -- nothing l u    
{-delete (avl-node N v L R) d = if v ≡ d then L else (avl-node N v L R)
delete (avl-node N v t R) d = if v ≡ d then t else (avl-node N v t R)
delete (avl-node N v L u) d = if v ≡ d then u else (avl-node N v L u)
delete (avl-node N v t u) d with v ≡ d
...| tt = (avl-node N (avl min u) t (delete u (avl-min u)))
...| ff rewrite ( d <  v) && ((balFactor (delete t d) u) < 2) = avl-node N v (delete t d) u
...| ff rewrite ((v < d) && ( (balFactor t (delete u A)) < 2)) = (avl-node N v t (delete u A))
...| ff rewrite ((d < v) && ((balFactor (left-avl u) (right-avl u)) < 0)) = balanceRR (avl-node N v (delete t d) u)
...| ff rewrite ((v < d) && (0 < (balFactor (left-avl t) (right-avl t)) )) = balanceLL (avl-node N v t (delete u A))
...| ff rewrite (d < v)                                       = balanceRL (avl-node N v (delete  t d) u)
...| ff rewrite (v < d)                                       = balanceLR (avl-node N v t (delete u A))
...| p = ?
-}{-        where dmin = delete u mu
              dt   = delete t d
              du   = delete u A
              mu   = avlmin u
-}
{-
 Test Functions. Not sure if we really need these, but they are thrown in

load : {ℂ} (A : Set ℂ) → avl →  A → avl
load t []     = t
load t (x:xs) = insert (load t xs) x

unload : {ℂ} (A : Set ℂ) → avl →  𝕃 A → avl
unload t []     = t
unload t (x:xs) = delete (unload t xs) x

sort : {ℂ} (A : Set ℂ) → 𝕃 A →  𝕃 A
sort = inorder . (load empty)

isBalanced L = True
isBalanced (N _ t u) = isBalanced t && isBalanced u && abs (balFactor t u) < 2
-}
