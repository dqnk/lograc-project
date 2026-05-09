module project where

open import Data.Nat     using (ℕ)
open import Data.List    using (List; []; _∷_; map)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty   using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary using (Decidable; DecidableEquality)
open import Data.List.Relation.Unary.Any using (Any; any?)
open import Data.List.Relation.Unary.All using (All; all?)
open import Relation.Nullary using (Dec; yes; no) renaming (¬_ to ~_)
open import Data.Bool using (Bool; true; false; not)
open import Relation.Binary using (Decidable; DecidableEquality)

data Formula : Set where
    Var : ℕ → Formula
    ¬_  : Formula → Formula
    _∧_ : Formula → Formula → Formula
    _∨_ : Formula → Formula → Formula

data Literal : Set where
    Var  : ℕ → Literal
    ¬Var : ℕ → Literal

data NNF : Set where
    lit : Literal → NNF
    _∧_ : NNF → NNF → NNF
    _∨_ : NNF → NNF → NNF


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