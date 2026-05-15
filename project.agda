module project where

open import Data.Nat     using (ℕ; _≟_; zero; suc; _+_)
open import Data.List    using (List; []; _∷_; map; _++_; length)
open import Data.Maybe   using (Maybe; just; nothing) renaming (map to map-maybe)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty   using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary using (Decidable; DecidableEquality)
open import Data.List.Relation.Unary.Any using (Any; any?)
open import Data.List.Relation.Unary.All using (All; all?)
open import Relation.Nullary using (Dec; yes; no) renaming (¬_ to ~_)
open import Data.Bool using (Bool; true; false; not)
open import Relation.Binary using (Decidable; DecidableEquality)

-- ============================================================
-- Problem 1

data Formula : Set where
    Var : ℕ → Formula
    ¬_  : Formula → Formula
    _∧_ : Formula → Formula → Formula
    _∨_ : Formula → Formula → Formula

-- ============================================================
-- Problem 2

data Literal : Set where
    Var  : ℕ → Literal
    ¬Var : ℕ → Literal

data NNF : Set where
    lit : Literal → NNF
    _∧_ : NNF → NNF → NNF
    _∨_ : NNF → NNF → NNF

-- ============================================================
-- Problem 3

mutual
    to-nnf : Formula → NNF
    to-nnf (Var n) = lit (Var n)
    to-nnf (¬ φ)   = to-nnf-neg φ
    to-nnf (a ∧ b) = to-nnf a ∧ to-nnf b
    to-nnf (a ∨ b) = to-nnf a ∨ to-nnf b

    to-nnf-neg : Formula → NNF
    to-nnf-neg (Var n) = lit (¬Var n)
    to-nnf-neg (¬ a)   = to-nnf a
    to-nnf-neg (a ∧ b) = to-nnf-neg a ∨ to-nnf-neg b
    to-nnf-neg (a ∨ b) = to-nnf-neg a ∧ to-nnf-neg b

-- ============================================================
-- Problem 4

-- data Dec (A : Set) : Set where
--   yes :   A   → Dec A
--   no  : (~ A) → Dec A

record DecType : Set₁ where
  field
    carr   : Set
    test-≡ : (x y : carr) → Dec (x ≡ y)

open DecType

module NoDupList where
  infix 4 _∈_

  data _∈_ {A : Set} : A → List A → Set where
    ∈-here  : {x : A} → {xs : List A} → x ∈ (x ∷ xs)
    ∈-there : {x y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

  data NoDup {A : Set} : List A → Set where
    []-nodup : NoDup []
    ∷-nodup : {x : A} {xs : List A} → NoDup xs → ~ (x ∈ xs) → NoDup (x ∷ xs)

module Assoc (K : DecType) (V : Set) where

  Assoc : Set
  Assoc = List (carr K × V)

  _∈_ : carr K → Assoc → Set
  k ∈ kvs = k NoDupList.∈ (map proj₁ kvs)

  lookup : {k : carr K} {kvs : Assoc} → k ∈ kvs → V
  lookup {kvs = []} ()
  lookup {kvs = (_ , v) ∷ _}    NoDupList.∈-here     = v
  lookup {kvs = (k , v) ∷ kvs} (NoDupList.∈-there p) = lookup p

  _∈?_ : (k : carr K) → (kvs : Assoc) → Dec (k ∈ kvs)
  k ∈? [] = no λ ()
  k ∈? ((k' , _) ∷ kvs) with K .test-≡ k k'
  ... | yes refl = yes NoDupList.∈-here
  ... | no p with k ∈? kvs
  ...           | yes q = yes (NoDupList.∈-there q)
  ...           | no q = no (λ { NoDupList.∈-here → p refl ; (NoDupList.∈-there r) → q r})

  _‼_ : (kvs : Assoc) → (k : carr K) → Maybe V
  kvs ‼ k with k ∈? kvs
  ... | yes p = just (lookup p)
  ... | no  _ = nothing

  _[_]≔_ : Assoc → carr K → V → Assoc
  kvs [ k ]≔ v with k ∈? kvs
  ... | yes _ = kvs
  ... | no  _ = (k , v) ∷ kvs

-- ============================================================
-- Problem 5

open Assoc (record { carr = ℕ ; test-≡ = _≟_ }) Bool
 
Assignment : Set
Assignment = Assoc
 
map-maybe2 : (Bool → Bool → Bool) → Maybe Bool → Maybe Bool → Maybe Bool
map-maybe2 f (just a) (just b) = just (f a b)
map-maybe2 _ _        _        = nothing
 
eval : Assignment → Formula → Maybe Bool
eval a (Var i)  = a ‼ i
eval a (¬ f)    = map-maybe not (eval a f)
eval a (f ∧ g)  = map-maybe2 Data.Bool._∧_ (eval a f) (eval a g)
eval a (f ∨ g)  = map-maybe2 Data.Bool._∨_ (eval a f) (eval a g)

-- ============================================================
-- Problem 6

eval-lit : Assignment → Literal → Maybe Bool
eval-lit a (Var i)  = a ‼ i
eval-lit a (¬Var i) = map-maybe not (a ‼ i)

eval-nnf : Assignment → NNF → Maybe Bool
eval-nnf a (lit l) = eval-lit a l
eval-nnf a (f ∧ g) = map-maybe2 Data.Bool._∧_ (eval-nnf a f) (eval-nnf a g)
eval-nnf a (f ∨ g) = map-maybe2 Data.Bool._∨_ (eval-nnf a f) (eval-nnf a g)

-- ============================================================
-- Problem 7

--data Literal : Set where
--    Var  : ℕ → Literal
--    ¬Var : ℕ → Literal

data Disjunct : Set where
    lit  : Literal → Disjunct
    _∨_  : Literal → Disjunct → Disjunct

data CNF : Set where
    disj : Disjunct → CNF
    _∧_  : Disjunct → CNF → CNF

-- ============================================================
-- Problem 8

eval-disj : Assignment → Disjunct → Maybe Bool
eval-disj a (lit l)  = eval-lit a l
eval-disj a (l ∨ d)  = map-maybe2 Data.Bool._∨_ (eval-lit a l) (eval-disj a d)

eval-cnf : Assignment → CNF → Maybe Bool
eval-cnf a (disj d) = eval-disj a d
eval-cnf a (d ∧ c) = map-maybe2 Data.Bool._∧_ (eval-disj a d) (eval-cnf a c)

-- =============================================================
-- Problem 9

data ClauseSat : Set where
    sat : ClauseSat
    fls : ClauseSat
    rem : Disjunct -> ClauseSat

data CNFSat : Set where 
    sat : CNFSat              
    fls : CNFSat              
    rem : CNF → CNFSat


Literal-≡ : (x y : Literal) → Dec (x ≡ y)
Literal-≡ (Var n)  (Var m)  with n ≟ m
... | yes refl = yes refl
... | no  p    = no (λ { refl → p refl })
Literal-≡ (¬Var n) (¬Var m) with n ≟ m
... | yes refl = yes refl
... | no  p    = no (λ { refl → p refl })
Literal-≡ (Var _)  (¬Var _) = no (λ ())
Literal-≡ (¬Var _) (Var _)  = no (λ ())

LiteralDec : DecType
LiteralDec = record { carr = Literal ; test-≡ = Literal-≡ } 


module LiteralSet where
    record LiteralSet : Set where
        constructor makeLiteralSet
        field
            literals : List Literal
            nodup : NoDupList.NoDup literals

    _∈?-lit_ : (l : Literal) → (ls : List Literal) → Dec (l NoDupList.∈ ls)
    l ∈?-lit [] = no (λ ())
    l ∈?-lit (l' ∷ ls) with Literal-≡ l l'
    ... | yes refl = yes NoDupList.∈-here
    ... | no  p    with l ∈?-lit ls
    ...   | yes q  = yes (NoDupList.∈-there q)
    ...   | no  q  = no (λ { NoDupList.∈-here → p refl ; (NoDupList.∈-there r) → q r })

    empty : LiteralSet
    empty = makeLiteralSet [] NoDupList.[]-nodup

    insert : Literal -> LiteralSet -> LiteralSet
    insert l (makeLiteralSet ls nd) with l ∈?-lit ls
    ... | yes _ = makeLiteralSet ls nd
    ... | no  p = makeLiteralSet (l ∷ ls) (NoDupList.∷-nodup nd p)

    size : LiteralSet -> ℕ
    size (makeLiteralSet literals _ ) = length literals  

    same-lit : Literal → Literal → Bool
    same-lit x y with DecType.test-≡ LiteralDec x y
    ... | yes _ = true
    ... | no  _ = false

    flip : Literal → Literal
    flip (Var n)  = ¬Var n
    flip (¬Var n) = Var n

    neg-lit : Literal → Literal → Bool
    neg-lit x y = same-lit x (flip y)

    contains : Literal -> LiteralSet -> Bool  
    contains l (makeLiteralSet literals _ ) = helper literals 
        where helper : List Literal -> Bool 
              helper [] = false 
              helper (l' ∷ ls) with same-lit l l'
              ... | true = true 
              ... | false = helper ls


open LiteralSet

assign-disj : Literal -> Disjunct -> ClauseSat
assign-disj l (lit x) with same-lit l x
... | true = sat 
... | false with neg-lit l x
...     | true = fls 
...     | false = rem (lit x)
assign-disj l (x ∨ d) with same-lit l x 
... | true = sat 
... | false with neg-lit l x 
...     | true = assign-disj l d 
...     | false with assign-disj l d 
...         | sat = sat 
...         | fls = rem (lit x)
...         | rem d' = rem (x ∨ d')


assign-cnf : Literal -> CNF -> CNFSat
assign-cnf l (disj x) with assign-disj l x
... | sat = sat 
... | fls = fls 
... | rem d = rem (disj d)
assign-cnf l (x ∧ cnf) with assign-disj l x 
... | sat = assign-cnf l cnf 
... | fls = fls 
... | rem d with assign-cnf l cnf 
... |   sat = rem (disj d)
... |   fls = fls 
... |   rem cnf' = rem (d ∧ cnf')



dpll-helper : ℕ -> ℕ -> CNF -> Assignment -> Maybe Assignment
dpll-helper zero _ _ _ = nothing
dpll-helper (suc k) n cnf assign with assign-cnf (Var n) cnf 
... | sat = just (assign [ n ]≔ true)
... | rem cnf' = dpll-helper k (suc n) cnf' (assign [ n ]≔ true) 
... | fls with assign-cnf (¬Var n) cnf 
...     | sat = just (assign [ n ]≔ false)
...     | fls = nothing 
...     | rem cnf' = dpll-helper k (suc n) cnf' (assign [ n ]≔ false)

size-disj : Disjunct → ℕ
size-disj (lit _)  = 1
size-disj (_ ∨ d)  = 1 + size-disj d

size-cnf : CNF → ℕ
size-cnf (disj d) = size-disj d
size-cnf (d ∧ c)  = size-disj d + size-cnf c

dpll : CNF -> Maybe Assignment
dpll cnf = dpll-helper (size-cnf cnf) zero cnf [] 

-- ============================================================
-- DPLL tests 
test-cnf : CNF
test-cnf = (Var 0 ∨ lit (Var 1)) ∧ disj (¬Var 0 ∨ lit (Var 2))

test-cnf-unsat : CNF
test-cnf-unsat = (lit (Var 0)) ∧ disj (lit (¬Var 0))

test1 : Maybe Assignment
test1 = dpll test-cnf

test2 : Maybe Assignment
test2 = dpll test-cnf-unsat