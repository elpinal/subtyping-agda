{-# OPTIONS --cubical --safe #-}
module Label where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude using (isProp; transport)

open import Cubical.Data.Nat using (ℕ; zero; suc; isSetℕ)
open import Cubical.Data.Nat.Order using (_<_; _≤_; ≤-refl; <-weaken; ≤<-trans; m≤n-isProp; <-asym)
open import Cubical.Data.Maybe using (Maybe; nothing; just)
open import Cubical.Data.Empty using () renaming (rec to ⊥-elim)

Label : Set
Label = ℕ

data Record (A : Set) : Label -> Set where
  nil : forall {l} -> Record A l
  cons : forall {l} -> Record A l -> (l' : Label) -> A -> .(l < l') -> Record A l'

data _∈_ {A : Set} (l₁ : Label) {l : Label} : Record A l -> Set where
  here : forall {l'} {r : Record A l'} {x lt} -> l₁ ≡ l -> l₁ ∈ cons r l x lt
  there : forall {l'} {r : Record A l'} {x lt} -> l₁ ∈ r -> l₁ ∈ cons r l x lt

find : forall {A} {l} -> (l₁ : Label) -> (r : Record A l) -> l₁ ∈ r -> A
find l₁ (cons _ _ x _) (here e) = x
find l₁ (cons r _ _ _) (there l₁∈r) = find l₁ r l₁∈r

∈-implies-≤ : forall {A} {l l'} {r : Record A l'} -> l ∈ r -> l ≤ l'
∈-implies-≤ {l = l} (here e) = transport (λ i -> l ≤ e i) ≤-refl
∈-implies-≤ (there {lt = lt} l∈r) = <-weaken (≤<-trans (∈-implies-≤ l∈r) lt)

l∈r-isProp : forall {A} l {l'} (r : Record A l') -> isProp (l ∈ r)
l∈r-isProp l {l'} (cons _ _ _ _) (here {lt = a} e1) (here {lt = b} e2) = λ i -> here {lt = m≤n-isProp a b i} (isSetℕ l l' e1 e2 i)
l∈r-isProp l (cons {l = l₁} r _ _ _) (here {lt = k} e) (there y) = ⊥-elim (<-asym k (transport (λ i -> e i ≤ l₁) (∈-implies-≤ y)))
l∈r-isProp l (cons {l = l₁} r _ _ _) (there {lt = k} x) (here e) = ⊥-elim (<-asym k (transport (λ i -> e i ≤ l₁) (∈-implies-≤ x)))
l∈r-isProp l (cons r _ _ _) (there {lt = k1} x) (there {lt = k2} y) = let a = l∈r-isProp l r x y in λ i → there {lt = m≤n-isProp k1 k2 i} (a i)
