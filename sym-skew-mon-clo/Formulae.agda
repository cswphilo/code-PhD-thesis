{-# OPTIONS --rewriting #-}

module Formulae where

open import Data.Maybe
open import Data.List
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Bool

open import Utilities

postulate At : Set

-- Formulae
data Fma : Set where 
  ` : At → Fma
  I : Fma
  _⊗_ : Fma → Fma → Fma
  _⊸_ : Fma → Fma → Fma

infix 22 _⊸_ _⊗_

-- Stoup
Stp : Set
Stp = Maybe Fma

pattern - = nothing

-- Context
Cxt : Set
Cxt = List Fma

-- Iterated ⊗
_⊗⋆_ : Fma → Cxt → Fma
A ⊗⋆ [] = A
A ⊗⋆ (B ∷ Γ) = (A ⊗ B) ⊗⋆ Γ

-- Iterated ⊸
_⊸⋆_ : Cxt → Fma → Fma
[] ⊸⋆ C = C
(A ∷ Γ) ⊸⋆ C = A ⊸ (Γ ⊸⋆ C)

infix 21 _⊗⋆_ _⊸⋆_

++⊸⋆ : (Γ Γ' : Cxt) (B : Fma)
  → (Γ ++ Γ') ⊸⋆ B ≡ Γ ⊸⋆ (Γ' ⊸⋆ B)
++⊸⋆ [] Γ' B = refl
++⊸⋆ (x ∷ Γ) Γ' B = cong (x ⊸_) (++⊸⋆ Γ Γ' B)

snoc⊸⋆ : (Γ : Cxt) (A B : Fma)
  → Γ ⊸⋆ A ⊸ B ≡ (Γ ∷ʳ A) ⊸⋆ B
snoc⊸⋆ [] A B = refl
snoc⊸⋆ (A' ∷ Γ) A B rewrite snoc⊸⋆ Γ A B = refl

snoc⊗⋆ : (Γ : Cxt) (A B : Fma)
  → (A ⊗⋆ (Γ ∷ʳ B)) ≡ (A ⊗⋆ Γ) ⊗ B
snoc⊗⋆ [] = λ A B → refl
snoc⊗⋆ (x ∷ Γ) = λ A → snoc⊗⋆ Γ (A ⊗ x)

{-# REWRITE ++⊸⋆ #-}
{-# REWRITE snoc⊗⋆ #-}
-- Predicates on formulae checking whether

-- the formula is not atomic
isn'tAt : Fma → Set
isn'tAt (` x) = ⊥
isn'tAt _ = ⊤

-- the formula is not in ⊗
isn't⊗ : Fma → Set
isn't⊗ (A ⊗ B) = ⊥
isn't⊗ _ = ⊤

-- the formula not in ­⊸
isn't⊸ : Fma → Set
isn't⊸ (A ⊸ B) = ⊥
isn't⊸ _ = ⊤

-- the formula is negtive, i.e the formula is not a unit nor a ⊗ (atoms are not polarized)
isNeg : Fma → Set
isNeg (` x) = ⊤
isNeg I = ⊥
isNeg (x ⊗ x₁) = ⊥
isNeg (x ⊸ x₁) = ⊤

is⊸ : Fma → Set
is⊸ (A ⊸ B) = ⊤
is⊸ _ = ⊥

isAt : Fma → Set
isAt (` x) = ⊤
isAt _ = ⊥

-- the formula is positive, i.e. the formula is not a ⊸ (atoms are not polarized)
isPos : Fma → Set
isPos (` x) = ⊤
isPos I = ⊤
isPos (x ⊗ x₁) = ⊤
isPos (x ⊸ x₁) = ⊥

isPPos : Fma → Set
isPPos (A ⊸ B) = ⊥
isPPos (` X) = ⊥
isPPos _ = ⊤

-- Predicate on stoups checking whether the stoup is irreducible,
-- i.e. it is either empty or a negative formula
isIrr : Stp → Set
isIrr - = ⊤
isIrr (just A) = isNeg (A)

isPosS : Stp → Set
isPosS (just x) = isPos x
isPosS - = ⊤

isIrr⊸ : Stp → Set
isIrr⊸ (just A) = is⊸ A
isIrr⊸ ─ = ⊤


isIrrAt : Stp → Set
isIrrAt (just A) = isAt A
isIrrAt ─ = ⊤

-- The type of irreducible stoups
Irr : Set
Irr = Σ Stp λ S → isIrr S

Irr⊸ : Set
Irr⊸ = Σ Stp λ S → isIrr⊸ S

PosS : Set
PosS = Σ Stp λ S → isPosS S

IrrAt : Set
IrrAt = Σ Stp λ S → isIrrAt S

irrisAt : ∀ S → isIrrAt S → isIrr S
irrisAt (just (` x)) y = y
irrisAt - y = y

irris⊸ : ∀ S → isIrr⊸ S → isIrr S
irris⊸ (just (x ⊸ x₁)) y = y
irris⊸ - y = y

irrAt : IrrAt → Irr
irrAt (S , p) = S , irrisAt S p

irr⊸ : Irr⊸ → Irr
irr⊸ (S , p) = S , irris⊸ S p

-- The type of positive formulae
Pos : Set
Pos = Σ Fma λ A → isPos A

PPos : Set
PPos = Σ Fma λ A → isPPos A

-- The type of negative formulae
Neg : Set
Neg = Σ Fma λ A → isNeg A

-- Projections and embeddings
irr : Irr → Stp
irr (S , s) = S

posS : PosS → Stp
posS (S , s) = S

ppos2pos : ∀ A → isPPos A → isPos A
ppos2pos I a = tt
ppos2pos (A ⊗ A₁) a = tt

pos : Pos → Fma
pos (A , a) = A

ppos : PPos → Fma
ppos (A , a) = A

ppos2 : PPos → Pos
ppos2 (A , a) = A , ppos2pos A a

neg : Neg → Fma
neg (A , a) = A

neg2irr : Neg → Irr
neg2irr (A , a) = just A , a 

--
fmaEQ : Fma → Fma → Bool
fmaEQ (` x) (` x₁) with x ≡ x₁
... | EQ = true
fmaEQ (` x) _ = false
fmaEQ I I = true
fmaEQ I _ = false
fmaEQ (A ⊗ A₁) (B ⊗ B₁)  with fmaEQ A B
... | true = fmaEQ A₁ B₁
... | false = false
fmaEQ (A ⊗ A₁) _ = false
fmaEQ (A ⊸ A₁) (B ⊸ B₁)  with fmaEQ A B
... | true = fmaEQ A₁ B₁
... | false = false
fmaEQ (A ⊸ A₁) _ = false
