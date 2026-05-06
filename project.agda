module project where
    open import Data.Nat using (ℕ)
    open import Data.List using (List; []; _∷_)
    open import Data.Maybe using (Maybe; just; nothing)
    open import Data.Product using (_×_; _,_)
    open import Data.Empty using (⊥)
    open import Relation.Binary.PropositionalEquality using (_≡_; refl)

    data Formula : Set where
        Var : ℕ -> Formula
        ¬ : Formula -> Formula
        _∧_ : Formula -> Formula -> Formula
        _∨_ : Formula -> Formula -> Formula

    data Literal : Set where
        Var : ℕ -> Literal
        ¬Var : ℕ -> Literal

    data NNF : Set where
        lit : Literal -> NNF
        _∧_ : NNF -> NNF -> NNF
        _∨_ : NNF -> NNF -> NNF

    mutual
      toNNF : Formula → NNF
      toNNF (Var n) = lit (Var n)
      toNNF (¬ φ)   = toNNFNeg φ
      toNNF (a ∧ b) = toNNF a ∧ toNNF b
      toNNF (a ∨ b) = toNNF a ∨ toNNF b

      toNNFNeg : Formula → NNF
      toNNFNeg (Var n) = lit (¬Var n)
      toNNFNeg (¬ a)   = toNNF a
      toNNFNeg (a ∧ b) = toNNFNeg a ∨ toNNFNeg b
      toNNFNeg (a ∨ b) = toNNFNeg a ∧ toNNFNeg b

    data Dec (A : Set) : Set where
        yes :  A  → Dec A
        no  : ¬A  → Dec A

    record DecType : Set₁ where
        field
          carr   : Set
          test-≡ : (x y : carr) → Dec (x ≡ y)

    open DecType

    module Assoc (K : DecType) (V : Set) where
        Assoc : Set
        Assoc = {!!}

        _∈_ : carr K → Assoc → Set
        k ∈ kvs = {!!}

        lookup : {k : carr K} {kvs : Assoc} → k ∈ kvs → V
        lookup p = {!!}

        _∈?_ : (k : carr K) → (kvs : Assoc) → Dec (k ∈ kvs)
        k ∈? kvs = {!!}

        _‼_ : (kvs : Assoc) → (k : carr K) → Maybe V
        kvs ‼ k = {!!}

        _[_]≔_ : Assoc → carr K → V → Assoc
        kvs [ k ]≔ v = {!!}