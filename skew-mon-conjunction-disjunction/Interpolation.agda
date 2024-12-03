{-# OPTIONS --rewriting #-}

module Interpolation where

open import Data.List renaming (map to mapList)
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding (_≗_)

open import Utilities 
open import Formulae
open import SeqCalc

t : Stp → Fma
t (just A) = A
t ─ = I

[_∣_] : Fma → Cxt → Fma
[ A ∣ [] ] = A
[ A ∣ B ∷ Γ ] = [ A ⊗ B ∣ Γ ]

var : Fma → List At
var (` x) = x ∷ [] 
var I = []
var (A ⊗ B) = var A ++ var B
var (A ∧ B) = var A ++ var B
var (A ∨ B) = var A ++ var B

varCxt : Cxt → List At
varCxt [] = []
varCxt (A ∷ Γ) = var A ++ varCxt Γ

varCxtAsso : (Γ Δ : Cxt) → varCxt (Γ ++ Δ) ≡ varCxt Γ ++ varCxt Δ
varCxtAsso [] Δ = refl
varCxtAsso (A ∷ Γ) Δ = cong₂ _++_ refl (varCxtAsso Γ Δ)

data sublistAt : List At → List At → Set where 
  stop : ∀ {xs} → sublistAt xs xs
  both : ∀ {xs ys} {x} → sublistAt xs ys → sublistAt (x ∷ xs) (x ∷ ys)
  ∷ʳ : ∀ {xs ys zs} {x} → sublistAt xs (ys ++ zs) → sublistAt xs (ys ++ x ∷ zs) 

[]sublistAt : (Γ : List At) → sublistAt [] Γ
[]sublistAt [] = stop
[]sublistAt (A ∷ Γ) = ∷ʳ {ys = []} ([]sublistAt Γ)

[]++[] : {X : Set} (xs ys : List X) → (eq : [] ≡ xs ++ ys) → xs ≡ [] × ys ≡ []
[]++[] [] [] refl = refl , refl

trivialInterpoEmpStp : {Γ : Cxt} {A : Fma} 
  → (f : - ∣ Γ ⊢ A) 
  → Σ (just I ∣ Γ ⊢ A) λ f1 → sublistAt [] (varCxt (Γ ++ A ∷ [])) × scut Ir f1 ≗ f
trivialInterpoEmpStp {Γ} {A} f = Il f , []sublistAt (varCxt (Γ ++ A ∷ [])) , refl
 
Ic : {S : Stp} {Γ1 Γ2 Γ : Cxt} {A B : Fma} 
  → (f : S ∣ Γ ⊢ B)
  → (eq : Γ ≡ Γ1 ++ A ∷ Γ2)
  → S ∣ Γ1 ++ I ∷ A ∷ Γ2 ⊢ B

Il-1 : {Γ : Cxt} {A : Fma} → (f : just I ∣ Γ ⊢ A) → - ∣ Γ ⊢ A

interpoScut : {S : Stp} (Γ1 Γ2 : Cxt) {Γ : Cxt} {A : Fma} 
  → (f : S ∣ Γ ⊢ A) 
  → (eq : Γ ≡ Γ1 ++ Γ2) -- given any partition
  → Σ Fma λ C
  → Σ (S ∣ Γ1 ⊢ C) λ f1 → Σ (just C ∣ Γ2 ⊢ A) λ f2
  → sublistAt (var C) (varCxt (t S ∷ Γ1)) × sublistAt (var C) (varCxt (Γ2 ++ A ∷ [])) × 
    scut f1 f2 ≗ subst (λ x → S ∣ x ⊢ A) eq f
interpoScut Γ1 Γ2 ax eq = {!   !}
interpoScut Γ1 Γ2 (pass f) eq = {!   !}
interpoScut Γ1 Γ2 Ir eq = {!   !}
interpoScut Γ1 Γ2 (Il f) refl with interpoScut Γ1 Γ2 f refl
... | C , f1 , f2 , sub1 , sub2 , eq = {!  !}
interpoScut Γ1 Γ2 (⊗r {Γ = Γ} {Δ} f g) eq with ++? Γ1 Γ Γ2 Δ eq
interpoScut .(Γ ++ Λ) Γ2 (⊗r {Γ = Γ} {.(Λ ++ Γ2)} f g) refl | inj₁ (Λ , refl , refl) with interpoScut Λ Γ2 g refl 
... | D , g1 , g2 , sub1 , sub2 , eq1 = {!  !}
-- with interpoScut Γ [] f refl | interpoScut Λ Γ2 g refl 
-- ... | C1 , f1 , f2 , sub1 , sub2 , eq1 | C2 , g1 , g2 , sub3 , sub4 , eq2 = 
--     C1 ⊗ C2 , ⊗r f1 g1 , ⊗l (⊗r f2 (pass g2)) , {!   !} , {!   !} , {!   !}
interpoScut Γ1 .(D ∷ Λ ++ Δ) (⊗r {Γ = .(Γ1 ++ D ∷ Λ)} {Δ} f g) refl | inj₂ (D , Λ , refl , refl) with interpoScut Γ1 (D ∷ Λ) f refl 
... | E , f1 , f2 , sub1 , sub2 , eq1 = E , f1 , ⊗r f2 g , sub1 , {!sub2   !} , {!   !}

-- interpoScut Γ1 Γ2 (⊗r {Γ = Γ} {Δ} f g) eq with ++? Γ1 Γ Γ2 Δ eq
-- interpoScut .(Γ ++ Λ) Γ2 (⊗r {Γ = Γ} {.(Λ ++ Γ2)} f g) refl | inj₁ (Λ , refl , refl) with interpoScut Γ [] f refl | interpoScut Λ Γ2 g refl 
-- ... | C1 , f1 , f2 , sub1 , sub2 , eq1 | C2 , g1 , g2 , sub3 , sub4 , eq2 = 
--     C1 ⊗ C2 , ⊗r f1 g1 , ⊗l (⊗r f2 (pass g2)) , {!   !} , {!   !} , {!   !}
-- interpoScut Γ1 .(D ∷ Λ ++ Δ) (⊗r {Γ = .(Γ1 ++ D ∷ Λ)} {Δ} f g) refl | inj₂ (D , Λ , refl , refl) with interpoScut Γ1 (D ∷ Λ) f refl | trivialInterpoEmpStp g
-- ... | C1 , f1 , f2 , sub1 , sub2 , eq1 | g2 , sub3 , eq2 = 
--     C1 ⊗ I , ⊗r f1 Ir , ⊗l (Ic {Γ1 = []} {Λ ++ Δ} (⊗r f2 (Il-1 g2)) refl) , sub1 , {!   !} , {!   !}
interpoScut Γ1 Γ2 (⊗l {B = B} f) refl with interpoScut (B ∷ Γ1) Γ2 f refl
... | C , f1 , f2 , sub1 , sub2 , eq = C , ⊗l f1 , f2 , sub1 , sub2 , ⊗l eq
interpoScut Γ1 Γ2 (∧r f g) refl with interpoScut Γ1 Γ2 f refl | interpoScut Γ1 Γ2 g refl
... | C , f1 , f2 , sub1 , sub2 , eq1 | D , g1 , g2 , sub3 , sub4 , eq2 = C ∧ D , ∧r f1 g1 , ∧r (∧l₁ f2) (∧l₂ g2) , {!   !} , {!   !} , ∧r eq1 eq2
interpoScut Γ1 Γ2 (∧l₁ f) refl with interpoScut Γ1 Γ2 f refl
... | C , f1 , f2 , sub1 , sub2 , eq = C , ∧l₁ f1 , f2 , {! sub1  !} , {! sub2  !} , ∧l₁ eq
interpoScut Γ1 Γ2 (∧l₂ f) refl with interpoScut Γ1 Γ2 f refl
... | C , f1 , f2 , sub1 , sub2 , eq = C , ∧l₂ f1 , f2 , {!  !} , sub2 , ∧l₂ eq
interpoScut Γ1 Γ2 (∨r₁ f) refl with interpoScut Γ1 Γ2 f refl
... | C , f1 , f2 , sub1 , sub2 , eq = C , f1 , ∨r₁ f2 , sub1 , {!  !} , {!   !}
interpoScut Γ1 Γ2 (∨r₂ f) refl with interpoScut Γ1 Γ2 f refl
... | C , f1 , f2 , sub1 , sub2 , eq = C , f1 , ∨r₂ f2 , sub1 , {!   !} , {!   !}
interpoScut Γ1 Γ2 (∨l f g) refl with interpoScut Γ1 Γ2 f refl | interpoScut Γ1 Γ2 g refl
... | C , f1 , f2 , sub1 , sub2 , eq1 | D , g1 , g2 , sub3 , sub4 , eq2 = C ∨ D , ∨l (∨r₁ f1) (∨r₂ g1) , ∨l f2 g2 , {!   !} , {!   !} , ∨l eq1 eq2
