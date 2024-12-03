{-# OPTIONS --rewriting #-}

module Focusemb where

open import Data.List renaming (map to mapList; zip to zipList)
open import Data.List.Relation.Unary.All renaming (map to mapAll; reduce to reduceAll)
open import Data.List.Properties
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Data.Product.Properties
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding (_≗_; [_])
open import Data.Bool hiding (_∧_; _∨_)

open import Utilities
open import Formulae
open import SeqCalc
open import Focusing
open import TagUntag
open import CheckFocus
open import FocusingProperties

{-
We show that focused derivations are in normal form, 
i.e. running the noralization algorithm on a focused derivation would
obtain a syntactically identical derivation, i.e. focus (emb-ri f) ≡ f
-}

-- focus (emb-ri f) ≡ f
mutual
  focusemb-∧rT* : {S : Irr} {Γ : Cxt} {A : Fma}{Ψ : List Pos}
    → (fs : All (_∣_⊢li_ (irr S) Γ) Ψ)
    → (SF : SubFmas Ψ A)
    → focus (emb-riT (∧rT* (proj₂ (tagF-fs {S} fs)) SF refl)) ≡ ∧r* fs SF
  focusemb-∧rT* {S} fs (conj {Φ} {Ψ} SF1 SF2) with fsDist-white Φ Ψ fs refl
  ... | fs1 , fs2 , refl 
    rewrite tagF-fs-All++ {S} fs1 fs2 |
            fsDist-refl (proj₂ (tagF-fs {S} fs1)) (proj₂ (tagF-fs {S} fs2)) = cong₂ ∧r (focusemb-∧rT* fs1 SF1) (focusemb-∧rT* fs2 SF2)
  focusemb-∧rT* (f2li ax ∷ []) stop = refl
  focusemb-∧rT* (f2li Ir ∷ []) stop = refl
  focusemb-∧rT* (f2li (pass f) ∷ []) stop = cong pass-ri (focusemb-li f)
  {- ⊗r -}
  focusemb-∧rT* {.(irr (just (` x) , tt)) , tt} (f2li {just (` x) , tt} (⊗r l ok refl f g) ∷ []) stop with f2fsT f
  focusemb-∧rT* {.(irr (just (` x) , tt)) , tt} (f2li {just (` x) , tt} (⊗r l ok refl f g) ∷ []) stop | Φ , fs , .(mapList (λ r → proj₂ r) Φ) , refl , SF , refl , refl with untag-tag fs
  ... | .((` x , tt) ∷ _) , f2li ax ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li ax ∷ fs') SF |
            f2fs-refl (f2li ax ∷ fs') SF refl |
            check-focus-ok-ax fs' |
            focusemb-ri g = refl
  ... | .((_ ⊗ _ , tt) ∷ _) , f2li (⊗r l {_ , tt} ok₁ refl f g') ∷ fs' , refl , refl
    rewrite focusemb-∧rT* (f2li (⊗r l ok₁ refl f g') ∷ fs') SF |
            f2fs-refl (f2li (⊗r l ok₁ refl f g') ∷ fs') SF refl |
            check-focus-ok-⊗r-atomS f fs' ok₁ g' |
            focusemb-ri g = refl
  ... | .((_ ∨ _ , tt) ∷ _) , f2li (∨r₁ l {_ , tt} {B = B} ok₁ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₁ l {B = B} ok₁ f) ∷ fs') SF |
            f2fs-refl (f2li (∨r₁ l {B = B} ok₁ f) ∷ fs') SF refl |
            check-focus-ok-∨r₁-atomS {B = B} f fs' ok₁ |
            focusemb-ri g = refl
  ... | .((_ ∨ _ , tt) ∷ _) , f2li (∨r₂ l {_ , tt} {A = A} ok₁ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₂ l {A = A} ok₁ f) ∷ fs') SF |
            f2fs-refl (f2li (∨r₂ l {A = A} ok₁ f) ∷ fs') SF refl |
            check-focus-ok-∨r₂-atomS {A = A} f fs' ok₁ |
            focusemb-ri g = refl
  focusemb-∧rT* {.(irr (just (x ∧ x₁) , tt)) , tt} (f2li {just (x ∧ x₁) , tt} (⊗r l ok refl f g) ∷ []) stop with f2fsT f
  focusemb-∧rT* {.(irr (just (x ∧ x₁) , tt)) , tt} (f2li {just (x ∧ x₁) , tt} (⊗r l ok refl f g) ∷ []) stop | Φ , fs , .(mapList (λ r → proj₂ r) Φ) , refl , SF , refl , refl with untag-tag fs
  ... | .((_ ⊗ _ , tt) ∷ _) , f2li (⊗r l {_ , tt} ok₁ refl f g') ∷ fs' , refl , refl
    rewrite focusemb-∧rT* (f2li (⊗r l ok₁ refl f g') ∷ fs') SF |
            f2fs-refl (f2li (⊗r l ok₁ refl f g') ∷ fs') SF refl |
            check-focus-ok-⊗r-∧S f fs' ok₁ g' |
            focusemb-ri g = refl
  ... | .(_ ∷ _) , f2li (∧l₁ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∧l₁ f) ∷ fs') SF |
            f2fs-refl (f2li (∧l₁ f) ∷ fs') SF refl |
            check-focus-ok-∧l₁ f fs' ok |
            focusemb-ri g = refl
  ... | .(_ ∷ _) , f2li (∧l₂ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∧l₂ f) ∷ fs') SF |
            f2fs-refl (f2li (∧l₂ f) ∷ fs') SF refl |
            check-focus-ok-∧l₂ f fs' ok |
            focusemb-ri g = refl
  ... | .((_ ∨ _ , tt) ∷ _) , f2li (∨r₁ l {_ , tt} {B = B} ok₁ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₁ l {B = B} ok₁ f) ∷ fs') SF |
            f2fs-refl (f2li (∨r₁ l {B = B} ok₁ f) ∷ fs') SF refl |
            check-focus-ok-∨r₁-∧S {B = B} f fs' ok₁ |
            focusemb-ri g = refl
  ... | .((_ ∨ _ , tt) ∷ _) , f2li (∨r₂ l {_ , tt} {A = A} ok₁ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₂ l {A = A} ok₁ f) ∷ fs') SF |
            f2fs-refl (f2li (∨r₂ l {A = A} ok₁ f) ∷ fs') SF refl |
            check-focus-ok-∨r₂-∧S {A = A} f fs' ok₁ |
            focusemb-ri g = refl
  focusemb-∧rT* {.(irr (- , tt)) , p} (f2li { - , tt} (⊗r l ok refl f g) ∷ []) stop with f2fsT f
  focusemb-∧rT* {.(irr (- , tt)) , tt} (f2li { - , tt} (⊗r l ok refl f g) ∷ []) stop | Φ , fs , .(mapList (λ r → proj₂ r) Φ) , refl , SF , refl , refl with untag-tag fs
  ... | .((I , tt) ∷ _) , f2li Ir ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li Ir ∷ fs') SF |
            f2fs-refl (f2li Ir ∷ fs') SF refl | 
            check-focus-ok-Ir fs' |
            focusemb-ri g = refl
  ... | .(_ ∷ _) , f2li (pass f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (pass f) ∷ fs') SF |
            f2fs-refl (f2li (pass f) ∷ fs') SF refl | 
            check-focus-ok-pass f fs' ok |
            focusemb-ri g = refl
  ... | .((_ ⊗ _ , tt) ∷ _) , f2li (⊗r l { - , tt} ok₁ refl f g') ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (⊗r l ok₁ refl f g') ∷ fs') SF |
            f2fs-refl (f2li (⊗r l ok₁ refl f g') ∷ fs') SF refl |
            check-focus-ok-⊗r-emptyS f fs' ok₁ g' |
            focusemb-ri g = refl
  ... | .((_ ∨ _ , tt) ∷ _) , f2li (∨r₁ l { - , tt}  {B = B} ok₁ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₁ l {B = B} ok₁ f) ∷ fs') SF |
            f2fs-refl (f2li (∨r₁ l {B = B} ok₁ f) ∷ fs') SF refl |
            check-focus-ok-∨r₁-emptyS {B = B} f fs' ok₁ |
            focusemb-ri g = refl
  ... | .((_ ∨ _ , tt) ∷ _) , f2li (∨r₂ l { - , tt} {A = A} ok₁ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₂ l {A = A} ok₁ f) ∷ fs') SF |
            f2fs-refl (f2li (∨r₂ l {A = A} ok₁ f) ∷ fs') SF refl |
            check-focus-ok-∨r₂-emptyS {A = A} f fs' ok₁ |
            focusemb-ri g = refl
  {- ⊗r -}
  focusemb-∧rT* (f2li (∧l₁ f) ∷ []) stop = cong ∧l₁-ri (focusemb-li f)
  focusemb-∧rT* (f2li (∧l₂ f) ∷ []) stop = cong ∧l₂-ri (focusemb-li f)
  {- ∨r₁ -}
  focusemb-∧rT* {.(irr (just (` x) , tt)) , tt} (f2li {just (` x) , tt} (∨r₁ l ok f) ∷ []) stop with f2fsT f
  focusemb-∧rT* {.(irr (just (` x) , tt)) , tt} (f2li {just (` x) , tt} (∨r₁ l ok f) ∷ []) stop | Φ , fs , .(mapList (λ r → proj₂ r) Φ) , refl , SF , refl , refl with untag-tag fs
  ... | .((` x , tt) ∷ _) , f2li ax ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li ax ∷ fs') SF |
            f2fs-refl (f2li ax ∷ fs') SF refl |
            check-focus-ok-ax fs' = refl
  ... | .((_ ⊗ _ , tt) ∷ _) , f2li (⊗r l {_ , tt} ok₁ refl f g) ∷ fs' , refl , refl
    rewrite focusemb-∧rT* (f2li (⊗r l ok₁ refl f g) ∷ fs') SF |
            f2fs-refl (f2li (⊗r l ok₁ refl f g) ∷ fs') SF refl |
            check-focus-ok-⊗r-atomS f fs' ok₁ g = refl
  ... | .((_ ∨ _ , tt) ∷ _) , f2li (∨r₁ l {_ , tt} {B = B} ok₁ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₁ l {B = B} ok₁ f) ∷ fs') SF |
            f2fs-refl (f2li (∨r₁ l {B = B} ok₁ f) ∷ fs') SF refl |
            check-focus-ok-∨r₁-atomS {B = B} f fs' ok₁ = refl
  ... | .((_ ∨ _ , tt) ∷ _) , f2li (∨r₂ l {_ , tt} {A = A} ok₁ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₂ l {A = A} ok₁ f) ∷ fs') SF |
            f2fs-refl (f2li (∨r₂ l {A = A} ok₁ f) ∷ fs') SF refl |
            check-focus-ok-∨r₂-atomS {A = A} f fs' ok₁ = refl
  focusemb-∧rT* {.(irr (just (x ∧ x₁) , tt)) , tt} (f2li {just (x ∧ x₁) , tt} (∨r₁ l ok f) ∷ []) stop with f2fsT f
  focusemb-∧rT* {.(irr (just (x ∧ x₁) , tt)) , tt} (f2li {just (x ∧ x₁) , tt} (∨r₁ l ok f) ∷ []) stop | Φ , fs , .(mapList (λ r → proj₂ r) Φ) , refl , SF , refl , refl with untag-tag fs
  ... | .((_ ⊗ _ , tt) ∷ _) , f2li (⊗r l {_ , tt} ok₁ refl f g) ∷ fs' , refl , refl
    rewrite focusemb-∧rT* (f2li (⊗r l ok₁ refl f g) ∷ fs') SF |
            f2fs-refl (f2li (⊗r l ok₁ refl f g) ∷ fs') SF refl |
            check-focus-ok-⊗r-∧S f fs' ok₁ g = refl
  ... | .(_ ∷ _) , f2li (∧l₁ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∧l₁ f) ∷ fs') SF |
            f2fs-refl (f2li (∧l₁ f) ∷ fs') SF refl |
            check-focus-ok-∧l₁ f fs' ok = refl
  ... | .(_ ∷ _) , f2li (∧l₂ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∧l₂ f) ∷ fs') SF |
            f2fs-refl (f2li (∧l₂ f) ∷ fs') SF refl |
            check-focus-ok-∧l₂ f fs' ok = refl
  ... | .((_ ∨ _ , tt) ∷ _) , f2li (∨r₁ l {_ , tt} {B = B} ok₁ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₁ l {B = B} ok₁ f) ∷ fs') SF |
            f2fs-refl (f2li (∨r₁ l {B = B} ok₁ f) ∷ fs') SF refl |
            check-focus-ok-∨r₁-∧S {B = B} f fs' ok₁ = refl
  ... | .((_ ∨ _ , tt) ∷ _) , f2li (∨r₂ l {_ , tt} {A = A} ok₁ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₂ l {A = A} ok₁ f) ∷ fs') SF |
            f2fs-refl (f2li (∨r₂ l {A = A} ok₁ f) ∷ fs') SF refl |
            check-focus-ok-∨r₂-∧S {A = A} f fs' ok₁ = refl
  focusemb-∧rT* {.(irr (- , tt)) , p} (f2li { - , tt} (∨r₁ l ok f) ∷ []) stop with f2fsT f
  focusemb-∧rT* {.(irr (- , tt)) , tt} (f2li { - , tt} (∨r₁ l ok f) ∷ []) stop | Φ , fs , .(mapList (λ r → proj₂ r) Φ) , refl , SF , refl , refl with untag-tag fs
  ... | .((I , tt) ∷ _) , f2li Ir ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li Ir ∷ fs') SF |
            f2fs-refl (f2li Ir ∷ fs') SF refl | 
            check-focus-ok-Ir fs' = refl
  ... | .(_ ∷ _) , f2li (pass f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (pass f) ∷ fs') SF |
            f2fs-refl (f2li (pass f) ∷ fs') SF refl | 
            check-focus-ok-pass f fs' ok = refl
  ... | .((_ ⊗ _ , tt) ∷ _) , f2li (⊗r l { - , tt} ok₁ refl f g) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (⊗r l ok₁ refl f g) ∷ fs') SF |
            f2fs-refl (f2li (⊗r l ok₁ refl f g) ∷ fs') SF refl |
            check-focus-ok-⊗r-emptyS f fs' ok₁ g = refl
  ... | .((_ ∨ _ , tt) ∷ _) , f2li (∨r₁ l { - , tt}  {B = B} ok₁ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₁ l {B = B} ok₁ f) ∷ fs') SF |
            f2fs-refl (f2li (∨r₁ l {B = B} ok₁ f) ∷ fs') SF refl |
            check-focus-ok-∨r₁-emptyS {B = B} f fs' ok₁ = refl
  ... | .((_ ∨ _ , tt) ∷ _) , f2li (∨r₂ l { - , tt} {A = A} ok₁ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₂ l {A = A} ok₁ f) ∷ fs') SF |
            f2fs-refl (f2li (∨r₂ l {A = A} ok₁ f) ∷ fs') SF refl |
            check-focus-ok-∨r₂-emptyS {A = A} f fs' ok₁ = refl
  {- ∨r₁ -}
  {- ∨r₂ -}  
  focusemb-∧rT* {.(irr (just (` x) , tt)) , tt} (f2li {just (` x) , tt} (∨r₂ l ok f) ∷ []) stop with f2fsT f
  focusemb-∧rT* {.(irr (just (` x) , tt)) , tt} (f2li {just (` x) , tt} (∨r₂ l ok f) ∷ []) stop | Φ , fs , .(mapList (λ r → proj₂ r) Φ) , refl , SF , refl , refl with untag-tag fs
  ... | .((` x , tt) ∷ _) , f2li ax ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li ax ∷ fs') SF |
            f2fs-refl (f2li ax ∷ fs') SF refl |
            check-focus-ok-ax fs' = refl
  ... | .((_ ⊗ _ , tt) ∷ _) , f2li (⊗r l {_ , tt} ok₁ refl f g) ∷ fs' , refl , refl
    rewrite focusemb-∧rT* (f2li (⊗r l ok₁ refl f g) ∷ fs') SF |
            f2fs-refl (f2li (⊗r l ok₁ refl f g) ∷ fs') SF refl |
            check-focus-ok-⊗r-atomS f fs' ok₁ g = refl
  ... | .((_ ∨ _ , tt) ∷ _) , f2li (∨r₁ l {_ , tt} {B = B} ok₁ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₁ l {B = B} ok₁ f) ∷ fs') SF |
            f2fs-refl (f2li (∨r₁ l {B = B} ok₁ f) ∷ fs') SF refl |
            check-focus-ok-∨r₁-atomS {B = B} f fs' ok₁ = refl
  ... | .((_ ∨ _ , tt) ∷ _) , f2li (∨r₂ l {_ , tt} {A = A} ok₁ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₂ l {A = A} ok₁ f) ∷ fs') SF |
            f2fs-refl (f2li (∨r₂ l {A = A} ok₁ f) ∷ fs') SF refl |
            check-focus-ok-∨r₂-atomS {A = A} f fs' ok₁ = refl
  focusemb-∧rT* {.(irr (just (x ∧ x₁) , tt)) , tt} (f2li {just (x ∧ x₁) , tt} (∨r₂ l ok f) ∷ []) stop with f2fsT f
  focusemb-∧rT* {.(irr (just (x ∧ x₁) , tt)) , tt} (f2li {just (x ∧ x₁) , tt} (∨r₂ l ok f) ∷ []) stop | Φ , fs , .(mapList (λ r → proj₂ r) Φ) , refl , SF , refl , refl with untag-tag fs
  ... | .((_ ⊗ _ , tt) ∷ _) , f2li (⊗r l {_ , tt} ok₁ refl f g) ∷ fs' , refl , refl
    rewrite focusemb-∧rT* (f2li (⊗r l ok₁ refl f g) ∷ fs') SF |
            f2fs-refl (f2li (⊗r l ok₁ refl f g) ∷ fs') SF refl |
            check-focus-ok-⊗r-∧S f fs' ok₁ g = refl
  ... | .(_ ∷ _) , f2li (∧l₁ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∧l₁ f) ∷ fs') SF |
            f2fs-refl (f2li (∧l₁ f) ∷ fs') SF refl |
            check-focus-ok-∧l₁ f fs' ok = refl
  ... | .(_ ∷ _) , f2li (∧l₂ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∧l₂ f) ∷ fs') SF |
            f2fs-refl (f2li (∧l₂ f) ∷ fs') SF refl |
            check-focus-ok-∧l₂ f fs' ok = refl
  ... | .((_ ∨ _ , tt) ∷ _) , f2li (∨r₁ l {_ , tt} {B = B} ok₁ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₁ l {B = B} ok₁ f) ∷ fs') SF |
            f2fs-refl (f2li (∨r₁ l {B = B} ok₁ f) ∷ fs') SF refl |
            check-focus-ok-∨r₁-∧S {B = B} f fs' ok₁ = refl
  ... | .((_ ∨ _ , tt) ∷ _) , f2li (∨r₂ l {_ , tt} {A = A} ok₁ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₂ l {A = A} ok₁ f) ∷ fs') SF |
            f2fs-refl (f2li (∨r₂ l {A = A} ok₁ f) ∷ fs') SF refl |
            check-focus-ok-∨r₂-∧S {A = A} f fs' ok₁ = refl
  focusemb-∧rT* {.(irr (- , tt)) , p} (f2li { - , tt} (∨r₂ l ok f) ∷ []) stop with f2fsT f
  focusemb-∧rT* {.(irr (- , tt)) , tt} (f2li { - , tt} (∨r₂ l ok f) ∷ []) stop | Φ , fs , .(mapList (λ r → proj₂ r) Φ) , refl , SF , refl , refl with untag-tag fs
  ... | .((I , tt) ∷ _) , f2li Ir ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li Ir ∷ fs') SF |
            f2fs-refl (f2li Ir ∷ fs') SF refl | 
            check-focus-ok-Ir fs' = refl
  ... | .(_ ∷ _) , f2li (pass f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (pass f) ∷ fs') SF |
            f2fs-refl (f2li (pass f) ∷ fs') SF refl | 
            check-focus-ok-pass f fs' ok = refl
  ... | .((_ ⊗ _ , tt) ∷ _) , f2li (⊗r l { - , tt} ok₁ refl f g) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (⊗r l ok₁ refl f g) ∷ fs') SF |
            f2fs-refl (f2li (⊗r l ok₁ refl f g) ∷ fs') SF refl |
            check-focus-ok-⊗r-emptyS f fs' ok₁ g = refl
  ... | .((_ ∨ _ , tt) ∷ _) , f2li (∨r₁ l { - , tt}  {B = B} ok₁ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₁ l {B = B} ok₁ f) ∷ fs') SF |
            f2fs-refl (f2li (∨r₁ l {B = B} ok₁ f) ∷ fs') SF refl |
            check-focus-ok-∨r₁-emptyS {B = B} f fs' ok₁ = refl
  ... | .((_ ∨ _ , tt) ∷ _) , f2li (∨r₂ l { - , tt} {A = A} ok₁ f) ∷ fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₂ l {A = A} ok₁ f) ∷ fs') SF |
            f2fs-refl (f2li (∨r₂ l {A = A} ok₁ f) ∷ fs') SF refl |
            check-focus-ok-∨r₂-emptyS {A = A} f fs' ok₁ = refl
  {- ∨r₂ -}

  focusemb-f : {S : Irr} {Γ : Cxt} {C : Pos}
    → (f : S ∣ Γ ⊢f C)
    → focus (emb-f f) ≡ li2ri (f2li f)
  focusemb-f ax = refl
  focusemb-f Ir = refl
  focusemb-f (pass f) = cong pass-ri (focusemb-li f)
  {- ⊗r -}
  focusemb-f (⊗r l ok refl f g) with f2fsT f
  ... | .[] , [] , Ψ , eq1 , SF , eq2 , eq3 = ⊥-elim (SubFmas[]-⊥ SF eq1)
  focusemb-f (⊗r l ok refl f g) | .((R , _ , tt) ∷ _) , ax ∷ fs , ._ , refl , SF , refl , refl with untag-tag fs
  focusemb-f (⊗r l ok refl f g) | .((R , _ , tt) ∷ _) , ax ∷ fs , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl
    rewrite focusemb-∧rT* (f2li ax ∷ fs') SF |
            f2fs-refl (f2li ax ∷ fs') SF refl |
            check-focus-ok-ax fs' |
            focusemb-ri g = refl
  focusemb-f (⊗r l ok refl f g) | .((R , I , tt) ∷ _) , Ir ∷ fs , ._ , refl , SF , refl , refl with untag-tag fs
  focusemb-f (⊗r l ok refl f g) | .((R , I , tt) ∷ _) , Ir ∷ fs , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl
    rewrite focusemb-∧rT* (f2li Ir ∷ fs') SF |
            f2fs-refl (f2li Ir ∷ fs') SF refl |
            check-focus-ok-Ir fs' |
            focusemb-ri g = refl
  focusemb-f (⊗r l ok refl f g) | .((P , _) ∷ _) , passT f' ∷ fs , ._ , refl , SF , refl , refl with untag-tag fs
  focusemb-f (⊗r l ok refl f g) | .((P , _) ∷ _) , passT f' ∷ fs , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl
    rewrite focusemb-∧rT* (f2li (pass f') ∷ fs') SF |
            f2fs-refl (f2li (pass f') ∷ fs') SF refl |
            check-focus-ok-pass f' fs' ok |
            focusemb-ri g = refl
  focusemb-f {S , p} (⊗r l ok refl f g) | .((R , _ ⊗ _ , tt) ∷ _) , ⊗rT l' ok₁ eq f' g₁ ∷ fs , ._ , refl , SF , refl , refl with untag-tag fs
  focusemb-f {just (` x) , tt} (⊗r ._ ok refl ._ g) | .((R , _ ⊗ _ , tt) ∷ proj₁ (tagF-fs fs')) , ⊗rT l' ok₁ refl f' g₁ ∷ .(subst (All (match-fT (just (` x) , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl
    rewrite focusemb-∧rT* (f2li (⊗r l' ok₁ refl f' g₁) ∷ fs') SF |
            f2fs-refl (f2li (⊗r l' ok₁ refl f' g₁) ∷ fs') SF refl |
            check-focus-ok-⊗r-atomS f' fs' ok₁ g₁ |
            focusemb-ri g = refl
  focusemb-f {just (x ∧ x₁) , tt} (⊗r ._ ok refl ._ g) | .((R , _ ⊗ _ , tt) ∷ proj₁ (tagF-fs fs')) , ⊗rT l' ok₁ refl f' g₁ ∷ .(subst (All (match-fT (just (x ∧ x₁) , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (⊗r l' ok₁ refl f' g₁) ∷ fs') SF |
            f2fs-refl (f2li (⊗r l' ok₁ refl f' g₁) ∷ fs') SF refl |
            check-focus-ok-⊗r-∧S f' fs' ok₁ g₁ |
            focusemb-ri g = refl
  focusemb-f { - , tt} (⊗r ._ ok refl ._ g) | .((R , _ ⊗ _ , tt) ∷ proj₁ (tagF-fs fs')) , ⊗rT l' ok₁ refl f' g₁ ∷ .(subst (All (match-fT (- , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (⊗r l' ok₁ refl f' g₁) ∷ fs') SF |
            f2fs-refl (f2li (⊗r l' ok₁ refl f' g₁) ∷ fs') SF refl |
            check-focus-ok-⊗r-emptyS f' fs' ok₁ g₁ |
            focusemb-ri g = refl
  focusemb-f (⊗r l ok refl f g) | .((C₁ , _) ∷ _) , ∧l₁T f' ∷ fs , ._ , refl , SF , refl , refl with untag-tag fs
  ... | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∧l₁ f') ∷ fs') SF |
            f2fs-refl (f2li (∧l₁ f') ∷ fs') SF refl |
            check-focus-ok-∧l₁ f' fs' ok |
            focusemb-ri g = refl 
  focusemb-f (⊗r l ok refl f g) | .((C₂ , _) ∷ _) , ∧l₂T f' ∷ fs , ._ , refl , SF , refl , refl with untag-tag fs
  ... | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∧l₂ f') ∷ fs') SF |
            f2fs-refl (f2li (∧l₂ f') ∷ fs') SF refl |
            check-focus-ok-∧l₂ f' fs' ok |
            focusemb-ri g = refl 
  focusemb-f (⊗r l ok refl f g) | .((R , _ ∨ _ , tt) ∷ _) , ∨r₁T l' ok₁ f' ∷ fs , .(mapList (λ r → proj₂ r) ((R , _ ∨ _ , tt) ∷ _)) , refl , SF , refl , refl with untag-tag fs
  focusemb-f {just (` x) , tt} (⊗r ._ ok refl ._ g) | .((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs')) , ∨r₁T l' {B = B} ok₁ f' ∷ .(subst (All (match-fT (just (` x) , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₁ l' ok₁ f') ∷ fs') SF |
            f2fs-refl (f2li (∨r₁ l' ok₁ f') ∷ fs') SF refl |
            check-focus-ok-∨r₁-atomS {B = B} f' fs' ok₁ |
            focusemb-ri g = refl
  focusemb-f {just (x ∧ x₁) , tt} (⊗r ._ ok refl ._ g) | .((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs')) , ∨r₁T l' {B = B} ok₁ f' ∷ .(subst (All (match-fT (just (x ∧ x₁) , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₁ l' ok₁ f') ∷ fs') SF |
            f2fs-refl (f2li (∨r₁ l' ok₁ f') ∷ fs') SF refl |
            check-focus-ok-∨r₁-∧S {B = B} f' fs' ok₁ |
            focusemb-ri g = refl
  focusemb-f { - , tt} (⊗r ._ ok refl ._ g) | .((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs')) , ∨r₁T l' {B = B} ok₁ f' ∷ .(subst (All (match-fT (- , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₁ l' ok₁ f') ∷ fs') SF |
            f2fs-refl (f2li (∨r₁ l' ok₁ f') ∷ fs') SF refl |
            check-focus-ok-∨r₁-emptyS {B = B} f' fs' ok₁ |
            focusemb-ri g = refl
  focusemb-f (⊗r l ok refl f g) | .((R , _ ∨ _ , tt) ∷ _) , ∨r₂T l' ok₁ f' ∷ fs , .(mapList (λ r → proj₂ r) ((R , _ ∨ _ , tt) ∷ _)) , refl , SF , refl , refl with untag-tag fs
  focusemb-f {just (` x) , tt} (⊗r ._ ok refl ._ g) | .((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs')) , ∨r₂T l' {A = A} ok₁ f' ∷ .(subst (All (match-fT (just (` x) , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₂ l' ok₁ f') ∷ fs') SF |
            f2fs-refl (f2li (∨r₂ l' ok₁ f') ∷ fs') SF refl |
            check-focus-ok-∨r₂-atomS {A = A} f' fs' ok₁ |
            focusemb-ri g = refl
  focusemb-f {just (x ∧ x₁) , tt} (⊗r ._ ok refl ._ g) | .((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs')) , ∨r₂T l' {A = A} ok₁ f' ∷ .(subst (All (match-fT (just (x ∧ x₁) , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₂ l' ok₁ f') ∷ fs') SF |
            f2fs-refl (f2li (∨r₂ l' ok₁ f') ∷ fs') SF refl |
            check-focus-ok-∨r₂-∧S {A = A} f' fs' ok₁ |
            focusemb-ri g = refl
  focusemb-f { - , tt} (⊗r ._ ok refl ._ g) | .((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs')) , ∨r₂T l' {A = A} ok₁ f' ∷ .(subst (All (match-fT (- , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₂ l' ok₁ f') ∷ fs') SF |
            f2fs-refl (f2li (∨r₂ l' ok₁ f') ∷ fs') SF refl |
            check-focus-ok-∨r₂-emptyS {A = A} f' fs' ok₁ |
            focusemb-ri g = refl
  {- ⊗r -}
  focusemb-f (∧l₁ f) = cong ∧l₁-ri (focusemb-li f)
  focusemb-f (∧l₂ f) = cong ∧l₂-ri (focusemb-li f)
  {- ∨r₁ -}
  focusemb-f (∨r₁ l ok f) with f2fsT f
  ... | .[] , [] , Ψ , eq1 , SF , eq2 , eq3 = ⊥-elim (SubFmas[]-⊥ SF eq1)
  focusemb-f (∨r₁ l ok f) | .((R , _ , tt) ∷ _) , ax ∷ fs , ._ , refl , SF , refl , refl with untag-tag fs
  focusemb-f (∨r₁ l ok f) | .((R , _ , tt) ∷ _) , ax ∷ fs , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl
    rewrite focusemb-∧rT* (f2li ax ∷ fs') SF |
            f2fs-refl (f2li ax ∷ fs') SF refl |
            check-focus-ok-ax fs' = refl
  focusemb-f (∨r₁ l ok f) | .((R , I , tt) ∷ _) , Ir ∷ fs , ._ , refl , SF , refl , refl with untag-tag fs
  focusemb-f (∨r₁ l ok f) | .((R , I , tt) ∷ _) , Ir ∷ fs , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl
    rewrite focusemb-∧rT* (f2li Ir ∷ fs') SF |
            f2fs-refl (f2li Ir ∷ fs') SF refl |
            check-focus-ok-Ir fs' = refl
  focusemb-f (∨r₁ l ok f) | .((P , _) ∷ _) , passT f' ∷ fs , ._ , refl , SF , refl , refl with untag-tag fs
  focusemb-f (∨r₁ l ok f) | .((P , _) ∷ _) , passT f' ∷ fs , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl
    rewrite focusemb-∧rT* (f2li (pass f') ∷ fs') SF |
            f2fs-refl (f2li (pass f') ∷ fs') SF refl |
            check-focus-ok-pass f' fs' ok = refl
  focusemb-f {S , p} (∨r₁ l ok f) | .((R , _ ⊗ _ , tt) ∷ _) , ⊗rT l' ok₁ eq f' g₁ ∷ fs , ._ , refl , SF , refl , refl with untag-tag fs
  focusemb-f {just (` x) , tt} (∨r₁ ._ ok ._) | .((R , _ ⊗ _ , tt) ∷ proj₁ (tagF-fs fs')) , ⊗rT l' ok₁ refl f' g₁ ∷ .(subst (All (match-fT (just (` x) , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl
    rewrite focusemb-∧rT* (f2li (⊗r l' ok₁ refl f' g₁) ∷ fs') SF |
            f2fs-refl (f2li (⊗r l' ok₁ refl f' g₁) ∷ fs') SF refl |
            check-focus-ok-⊗r-atomS f' fs' ok₁ g₁ = refl
  focusemb-f {just (x ∧ x₁) , tt} (∨r₁ ._ ok ._) | .((R , _ ⊗ _ , tt) ∷ proj₁ (tagF-fs fs')) , ⊗rT l' ok₁ refl f' g₁ ∷ .(subst (All (match-fT (just (x ∧ x₁) , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (⊗r l' ok₁ refl f' g₁) ∷ fs') SF |
            f2fs-refl (f2li (⊗r l' ok₁ refl f' g₁) ∷ fs') SF refl |
            check-focus-ok-⊗r-∧S f' fs' ok₁ g₁ = refl
  focusemb-f { - , tt} (∨r₁ ._ ok ._) | .((R , _ ⊗ _ , tt) ∷ proj₁ (tagF-fs fs')) , ⊗rT l' ok₁ refl f' g₁ ∷ .(subst (All (match-fT (- , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (⊗r l' ok₁ refl f' g₁) ∷ fs') SF |
            f2fs-refl (f2li (⊗r l' ok₁ refl f' g₁) ∷ fs') SF refl |
            check-focus-ok-⊗r-emptyS f' fs' ok₁ g₁ = refl
  focusemb-f (∨r₁ l ok f) | .((C₁ , _) ∷ _) , ∧l₁T f' ∷ fs , ._ , refl , SF , refl , refl with untag-tag fs
  ... | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∧l₁ f') ∷ fs') SF |
            f2fs-refl (f2li (∧l₁ f') ∷ fs') SF refl |
            check-focus-ok-∧l₁ f' fs' ok = refl 
  focusemb-f (∨r₁ l ok f) | .((C₂ , _) ∷ _) , ∧l₂T f' ∷ fs , ._ , refl , SF , refl , refl with untag-tag fs
  ... | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∧l₂ f') ∷ fs') SF |
            f2fs-refl (f2li (∧l₂ f') ∷ fs') SF refl |
            check-focus-ok-∧l₂ f' fs' ok = refl 
  focusemb-f (∨r₁ l ok f) | .((R , _ ∨ _ , tt) ∷ _) , ∨r₁T l' ok₁ f' ∷ fs , .(mapList (λ r → proj₂ r) ((R , _ ∨ _ , tt) ∷ _)) , refl , SF , refl , refl with untag-tag fs
  focusemb-f {just (` x) , tt} (∨r₁ ._ ok ._) | .((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs')) , ∨r₁T l' {B = B} ok₁ f' ∷ .(subst (All (match-fT (just (` x) , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₁ l' ok₁ f') ∷ fs') SF |
            f2fs-refl (f2li (∨r₁ l' ok₁ f') ∷ fs') SF refl |
            check-focus-ok-∨r₁-atomS {B = B} f' fs' ok₁ = refl
  focusemb-f {just (x ∧ x₁) , tt} (∨r₁ ._ ok ._) | .((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs')) , ∨r₁T l' {B = B} ok₁ f' ∷ .(subst (All (match-fT (just (x ∧ x₁) , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₁ l' ok₁ f') ∷ fs') SF |
            f2fs-refl (f2li (∨r₁ l' ok₁ f') ∷ fs') SF refl |
            check-focus-ok-∨r₁-∧S {B = B} f' fs' ok₁ = refl
  focusemb-f { - , tt} (∨r₁ ._ ok ._) | .((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs')) , ∨r₁T l' {B = B} ok₁ f' ∷ .(subst (All (match-fT (- , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₁ l' ok₁ f') ∷ fs') SF |
            f2fs-refl (f2li (∨r₁ l' ok₁ f') ∷ fs') SF refl |
            check-focus-ok-∨r₁-emptyS {B = B} f' fs' ok₁ = refl
  focusemb-f (∨r₁ l ok f) | .((R , _ ∨ _ , tt) ∷ _) , ∨r₂T l' ok₁ f' ∷ fs , .(mapList (λ r → proj₂ r) ((R , _ ∨ _ , tt) ∷ _)) , refl , SF , refl , refl with untag-tag fs
  focusemb-f {just (` x) , tt} (∨r₁ ._ ok ._) | .((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs')) , ∨r₂T l' {A = A} ok₁ f' ∷ .(subst (All (match-fT (just (` x) , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₂ l' ok₁ f') ∷ fs') SF |
            f2fs-refl (f2li (∨r₂ l' ok₁ f') ∷ fs') SF refl |
            check-focus-ok-∨r₂-atomS {A = A} f' fs' ok₁ = refl
  focusemb-f {just (x ∧ x₁) , tt} (∨r₁ ._ ok ._) | .((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs')) , ∨r₂T l' {A = A} ok₁ f' ∷ .(subst (All (match-fT (just (x ∧ x₁) , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₂ l' ok₁ f') ∷ fs') SF |
            f2fs-refl (f2li (∨r₂ l' ok₁ f') ∷ fs') SF refl |
            check-focus-ok-∨r₂-∧S {A = A} f' fs' ok₁ = refl
  focusemb-f { - , tt} (∨r₁ ._ ok ._) | .((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs')) , ∨r₂T l' {A = A} ok₁ f' ∷ .(subst (All (match-fT (- , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₂ l' ok₁ f') ∷ fs') SF |
            f2fs-refl (f2li (∨r₂ l' ok₁ f') ∷ fs') SF refl |
            check-focus-ok-∨r₂-emptyS {A = A} f' fs' ok₁ = refl
  {- ∨r₁ -}
  {- ∨r₂ -}
  focusemb-f (∨r₂ l ok f) with f2fsT f
  ... | .[] , [] , Ψ , eq1 , SF , eq2 , eq3 = ⊥-elim (SubFmas[]-⊥ SF eq1)
  focusemb-f (∨r₂ l ok f) | .((R , _ , tt) ∷ _) , ax ∷ fs , ._ , refl , SF , refl , refl with untag-tag fs
  focusemb-f (∨r₂ l ok f) | .((R , _ , tt) ∷ _) , ax ∷ fs , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl
    rewrite focusemb-∧rT* (f2li ax ∷ fs') SF |
            f2fs-refl (f2li ax ∷ fs') SF refl |
            check-focus-ok-ax fs' = refl
  focusemb-f (∨r₂ l ok f) | .((R , I , tt) ∷ _) , Ir ∷ fs , ._ , refl , SF , refl , refl with untag-tag fs
  focusemb-f (∨r₂ l ok f) | .((R , I , tt) ∷ _) , Ir ∷ fs , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl
    rewrite focusemb-∧rT* (f2li Ir ∷ fs') SF |
            f2fs-refl (f2li Ir ∷ fs') SF refl |
            check-focus-ok-Ir fs' = refl
  focusemb-f (∨r₂ l ok f) | .((P , _) ∷ _) , passT f' ∷ fs , ._ , refl , SF , refl , refl with untag-tag fs
  focusemb-f (∨r₂ l ok f) | .((P , _) ∷ _) , passT f' ∷ fs , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl
    rewrite focusemb-∧rT* (f2li (pass f') ∷ fs') SF |
            f2fs-refl (f2li (pass f') ∷ fs') SF refl |
            check-focus-ok-pass f' fs' ok = refl
  focusemb-f {S , p} (∨r₂ l ok f) | .((R , _ ⊗ _ , tt) ∷ _) , ⊗rT l' ok₁ eq f' g₁ ∷ fs , ._ , refl , SF , refl , refl with untag-tag fs
  focusemb-f {just (` x) , tt} (∨r₂ ._ ok ._) | .((R , _ ⊗ _ , tt) ∷ proj₁ (tagF-fs fs')) , ⊗rT l' ok₁ refl f' g₁ ∷ .(subst (All (match-fT (just (` x) , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl
    rewrite focusemb-∧rT* (f2li (⊗r l' ok₁ refl f' g₁) ∷ fs') SF |
            f2fs-refl (f2li (⊗r l' ok₁ refl f' g₁) ∷ fs') SF refl |
            check-focus-ok-⊗r-atomS f' fs' ok₁ g₁ = refl
  focusemb-f {just (x ∧ x₁) , tt} (∨r₂ ._ ok ._) | .((R , _ ⊗ _ , tt) ∷ proj₁ (tagF-fs fs')) , ⊗rT l' ok₁ refl f' g₁ ∷ .(subst (All (match-fT (just (x ∧ x₁) , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (⊗r l' ok₁ refl f' g₁) ∷ fs') SF |
            f2fs-refl (f2li (⊗r l' ok₁ refl f' g₁) ∷ fs') SF refl |
            check-focus-ok-⊗r-∧S f' fs' ok₁ g₁ = refl
  focusemb-f { - , tt} (∨r₂ ._ ok ._) | .((R , _ ⊗ _ , tt) ∷ proj₁ (tagF-fs fs')) , ⊗rT l' ok₁ refl f' g₁ ∷ .(subst (All (match-fT (- , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (⊗r l' ok₁ refl f' g₁) ∷ fs') SF |
            f2fs-refl (f2li (⊗r l' ok₁ refl f' g₁) ∷ fs') SF refl |
            check-focus-ok-⊗r-emptyS f' fs' ok₁ g₁ = refl
  focusemb-f (∨r₂ l ok f) | .((C₁ , _) ∷ _) , ∧l₁T f' ∷ fs , ._ , refl , SF , refl , refl with untag-tag fs
  ... | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∧l₁ f') ∷ fs') SF |
            f2fs-refl (f2li (∧l₁ f') ∷ fs') SF refl |
            check-focus-ok-∧l₁ f' fs' ok = refl 
  focusemb-f (∨r₂ l ok f) | .((C₂ , _) ∷ _) , ∧l₂T f' ∷ fs , ._ , refl , SF , refl , refl with untag-tag fs
  ... | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∧l₂ f') ∷ fs') SF |
            f2fs-refl (f2li (∧l₂ f') ∷ fs') SF refl |
            check-focus-ok-∧l₂ f' fs' ok = refl 
  focusemb-f (∨r₂ l ok f) | .((R , _ ∨ _ , tt) ∷ _) , ∨r₁T l' ok₁ f' ∷ fs , .(mapList (λ r → proj₂ r) ((R , _ ∨ _ , tt) ∷ _)) , refl , SF , refl , refl with untag-tag fs
  focusemb-f {just (` x) , tt} (∨r₂ ._ ok ._) | .((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs')) , ∨r₁T l' {B = B} ok₁ f' ∷ .(subst (All (match-fT (just (` x) , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₁ l' ok₁ f') ∷ fs') SF |
            f2fs-refl (f2li (∨r₁ l' ok₁ f') ∷ fs') SF refl |
            check-focus-ok-∨r₁-atomS {B = B} f' fs' ok₁ = refl
  focusemb-f {just (x ∧ x₁) , tt} (∨r₂ ._ ok ._) | .((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs')) , ∨r₁T l' {B = B} ok₁ f' ∷ .(subst (All (match-fT (just (x ∧ x₁) , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₁ l' ok₁ f') ∷ fs') SF |
            f2fs-refl (f2li (∨r₁ l' ok₁ f') ∷ fs') SF refl |
            check-focus-ok-∨r₁-∧S {B = B} f' fs' ok₁ = refl
  focusemb-f { - , tt} (∨r₂ ._ ok ._) | .((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs')) , ∨r₁T l' {B = B} ok₁ f' ∷ .(subst (All (match-fT (- , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₁ l' ok₁ f') ∷ fs') SF |
            f2fs-refl (f2li (∨r₁ l' ok₁ f') ∷ fs') SF refl |
            check-focus-ok-∨r₁-emptyS {B = B} f' fs' ok₁ = refl
  focusemb-f (∨r₂ l ok f) | .((R , _ ∨ _ , tt) ∷ _) , ∨r₂T l' ok₁ f' ∷ fs , .(mapList (λ r → proj₂ r) ((R , _ ∨ _ , tt) ∷ _)) , refl , SF , refl , refl with untag-tag fs
  focusemb-f {just (` x) , tt} (∨r₂ ._ ok ._) | .((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs')) , ∨r₂T l' {A = A} ok₁ f' ∷ .(subst (All (match-fT (just (` x) , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₂ l' ok₁ f') ∷ fs') SF |
            f2fs-refl (f2li (∨r₂ l' ok₁ f') ∷ fs') SF refl |
            check-focus-ok-∨r₂-atomS {A = A} f' fs' ok₁ = refl
  focusemb-f {just (x ∧ x₁) , tt} (∨r₂ ._ ok ._) | .((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs')) , ∨r₂T l' {A = A} ok₁ f' ∷ .(subst (All (match-fT (just (x ∧ x₁) , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₂ l' ok₁ f') ∷ fs') SF |
            f2fs-refl (f2li (∨r₂ l' ok₁ f') ∷ fs') SF refl |
            check-focus-ok-∨r₂-∧S {A = A} f' fs' ok₁ = refl
  focusemb-f { - , tt} (∨r₂ ._ ok ._) | .((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs')) , ∨r₂T l' {A = A} ok₁ f' ∷ .(subst (All (match-fT (- , tt) _)) refl (proj₂ (tagF-fs fs'))) , ._ , refl , SF , refl , refl | Ψ , fs' , refl , refl 
    rewrite focusemb-∧rT* (f2li (∨r₂ l' ok₁ f') ∷ fs') SF |
            f2fs-refl (f2li (∨r₂ l' ok₁ f') ∷ fs') SF refl |
            check-focus-ok-∨r₂-emptyS {A = A} f' fs' ok₁ = refl
  {- ∨r₂ -}
  focusemb-li : {S : Stp} {Γ : Cxt} {C : Pos}
    → (f : S ∣ Γ ⊢li C)
    →  focus (emb-li f) ≡ li2ri f
  focusemb-li (⊗l f) = cong ⊗l-ri (focusemb-li f)
  focusemb-li (Il f) = cong Il-ri (focusemb-li f)
  focusemb-li {C = ` x , snd} (∨l f g) = cong₂ ∨l-ri (focusemb-li f) (focusemb-li g)
  focusemb-li {C = I , snd} (∨l f g) = cong₂ ∨l-ri (focusemb-li f) (focusemb-li g)
  focusemb-li {C = A ⊗ A₁ , snd} (∨l f g) = cong₂ ∨l-ri (focusemb-li f) (focusemb-li g)
  focusemb-li {C = A ∨ A₁ , snd} (∨l f g) = cong₂ ∨l-ri (focusemb-li f) (focusemb-li g)
  focusemb-li (f2li f) = focusemb-f f

  focusemb-ri : {S : Stp} {Γ : Cxt} {C : Fma}
    → (f : S ∣ Γ ⊢ri C)
    → focus (emb-ri f) ≡ f
  focusemb-ri (∧r f g) = cong₂ ∧r (focusemb-ri f) (focusemb-ri g)
  focusemb-ri (li2ri f) = focusemb-li f                                   