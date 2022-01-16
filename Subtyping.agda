{-# OPTIONS --cubical --safe #-}
module Subtyping where

open import Cubical.Core.Everything hiding (Type)
open import Cubical.Foundations.Prelude using (refl; sym; symP; cong; _∙_; transport; subst; transportRefl; transport-filler; toPathP; fromPathP; congP)
open import Cubical.Foundations.Transport using (transport⁻Transport)

open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; +-comm; snotz; znots; +-suc; +-zero; injSuc; isSetℕ)
open import Cubical.Data.Nat.Order using (_≟_; lt; eq; gt; ≤-k+; ≤-+k; ≤-trans; pred-≤-pred; _≤_; _<_; ¬m+n<m; ¬-<-zero; suc-≤-suc; <-k+; <-+k; zero-≤; m≤n-isProp; <≤-trans; ≤-refl)
open import Cubical.Data.Fin using (Fin; toℕ; fzero; fsuc; Fin-fst-≡)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd; ΣPathP)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
import Cubical.Data.Empty as Empty

-- A term with `n` free variables.
data Term (n : ℕ) : Set where
  var : Fin n -> Term n
  abs : Term (suc n) -> Term n
  _·_ : Term n -> Term n -> Term n

shift : forall {m : ℕ} (n : ℕ) (i : Fin (suc m)) (e : Term m) -> Term (m + n)
shift {m} n i (var j)
  with toℕ i ≟ toℕ j
... | lt _ = var (toℕ j + n , ≤-+k (snd j))
... | eq _ = var (toℕ j + n , ≤-+k (snd j))
... | gt _ = var (toℕ j , ≤-trans (snd j) (n , +-comm n m))
shift n i (abs e) = abs (shift n (fsuc i) e)
shift n i (e · e₁) = shift n i e · shift n i e₁

subst′ : forall {m n : ℕ}
  -> (e' : Term m)
  -> (i : Fin (suc n))
  -> (e1 : Term (suc (n + m)))
  -> Term (n + m)
subst′ {m} {n} e' i (var j) with toℕ j ≟ toℕ i
... | lt j<i = var (toℕ j , <≤-trans j<i (pred-≤-pred (≤-trans (snd i) (suc-≤-suc (m , +-comm m n)))))
... | eq _ = transport (λ i₁ → Term (+-comm m n i₁)) (shift n fzero e')
... | gt i<j with j
...             | zero , _        = Empty.rec (¬-<-zero i<j)
...             | suc fst₁ , snd₁ = var (fst₁ , pred-≤-pred snd₁)
subst′ e' i (abs e1) = abs (subst′ e' (fsuc i) e1)
subst′ e' i (e1 · e2) = subst′ e' i e1 · subst′ e' i e2

infix 3 _▷_

data _▷_ {n : ℕ} : Term n -> Term n -> Set where
  beta/=> : forall {e1 : Term (suc n)} {e2 : Term n} -> abs e1 · e2 ▷ subst′ e2 fzero e1
  cong/app : forall {e1 e1' e2 : Term n} -> e1 ▷ e1' -> e1 · e2 ▷ e1' · e2

data Base : Set where
  Unit : Base
  Int : Base

infixr 8 _=>_

data Type : Set where
  base : Base -> Type
  Top : Type
  _=>_ : Type -> Type -> Type

data Context : ℕ -> Set where
  [] : Context 0
  _∷_ : forall {n} -> Type -> Context n -> Context (suc n)

data _[_]=_ : forall {n} -> Context n -> Fin n -> Type -> Set where
  here  : forall {n} A (G : Context n)         -> (A ∷ G) [ 0 , suc-≤-suc zero-≤ ]= A
  there : forall {n} {A} B {G : Context n} {i} -> G [ i ]= A -> (B ∷ G) [ fsuc i ]= A

lookup : forall {n} -> Context n -> Fin n -> Type
lookup [] (fst₁ , snd₁) = Empty.rec (¬-<-zero snd₁)
lookup (A ∷ G) (zero , snd₁) = A
lookup (A ∷ G) (suc fst₁ , snd₁) = lookup G (fst₁ , pred-≤-pred snd₁)

lookup-[]= : forall {n} (G : Context n) i -> G [ i ]= lookup G i
lookup-[]= [] (fst₁ , snd₁) = Empty.rec (¬-<-zero snd₁)
lookup-[]= (A ∷ G) (zero , snd₁) = subst (λ f -> (A ∷ G) [ f ]= A) (Fin-fst-≡ refl) (here A G)
lookup-[]= (A ∷ G) (suc fst₁ , snd₁) = subst (λ f -> (A ∷ G) [ f ]= lookup G (fst₁ , pred-≤-pred snd₁)) (Fin-fst-≡ refl) (there A (lookup-[]= G (fst₁ , pred-≤-pred snd₁)))

_++_ : forall {m n} -> Context m -> Context n -> Context (m + n)
[] ++ G2       = G2
(A ∷ G1) ++ G2 = A ∷ (G1 ++ G2)

++-[]= : forall {m n} {G : Context m} (G' : Context n) {j : Fin m} {A}
  -> G [ j ]= A
  -> (G' ++ G) [ n + toℕ j , <-k+ (snd j) ]= A
++-[]= [] l = subst (λ f → _ [ f ]= _) (Fin-fst-≡ refl) l
++-[]= {G = G} (C ∷ G') {A = A} l = subst (λ f → ((C ∷ G') ++ G) [ f ]= A) (Fin-fst-≡ refl) (there C (++-[]= G' l))

inserts : forall {m n} -> Fin (suc m) -> Context n -> Context m -> Context (m + n)
inserts {m} {n} (zero , snd₁) G' G   = subst Context (+-comm n m) (G' ++ G)
inserts (suc fst₁ , snd₁) G' []      = Empty.rec (¬-<-zero (pred-≤-pred snd₁))
inserts (suc fst₁ , snd₁) G' (A ∷ G) = A ∷ inserts (fst₁ , pred-≤-pred snd₁) G' G

inserts-[]=-unaffected : forall {m n} (G : Context m) (G' : Context n) {j : Fin m} (i : Fin (suc m)) {A}
  -> toℕ j < toℕ i
  -> G [ j ]= A
  -> inserts i G' G [ toℕ j , ≤-trans (snd j) (n , +-comm n m) ]= A
inserts-[]=-unaffected (A ∷ G) G' (zero , snd₁) j<i (here .A .G) = Empty.rec (¬-<-zero j<i)
inserts-[]=-unaffected (A ∷ G) G' (suc fst₁ , snd₁) j<i (here .A .G) = subst (λ f → inserts (suc fst₁ , snd₁) G' (A ∷ G) [ f ]= A) (Fin-fst-≡ refl) (here A (inserts (fst₁ , pred-≤-pred snd₁) G' G))
inserts-[]=-unaffected (B ∷ _) G' (zero , snd₁) j<i (there .B l) = Empty.rec (¬-<-zero j<i)
inserts-[]=-unaffected (B ∷ G) G' (suc fst₁ , snd₁) {A = A} j<i (there .B l) = subst (λ f → inserts (suc fst₁ , snd₁) G' (B ∷ G) [ f ]= A) (Fin-fst-≡ refl) (there B (inserts-[]=-unaffected G G' (fst₁ , pred-≤-pred snd₁) (pred-≤-pred j<i) l))

helper1 : forall m n (j : Fin m) -> PathP (λ i -> Fin (+-comm n m i)) (n + toℕ j , <-k+ (snd j)) (toℕ j + n , ≤-+k (snd j))
helper1 m n j = ΣPathP (+-comm n (toℕ j) , toPathP (m≤n-isProp _ _))

helper2 : forall m n (G : Context m) (G' : Context n) -> PathP (λ i → Context (+-comm n m i)) (G' ++ G) (subst Context (+-comm n m) (G' ++ G))
helper2 m n G G' = toPathP refl

inserts-[]=-shifted : forall {m n} (G : Context m) (G' : Context n) {j : Fin m} (i : Fin (suc m)) {A}
  -> toℕ i ≤ toℕ j
  -> G [ j ]= A
  -> inserts i G' G [ toℕ j + n , ≤-+k (snd j) ]= A
inserts-[]=-shifted {m} {n} G G' {j} (zero , snd₁) {A} i≤j l = transport (λ i -> helper2 m n G G' i [ helper1 m n j i ]= A) (++-[]= G' l)
inserts-[]=-shifted (B ∷ G) G' (suc fst₁ , snd₁) i≤j (here .B .G) = Empty.rec (¬-<-zero i≤j)
inserts-[]=-shifted (B ∷ G) G' {j = suc fst₂ , snd₂} (suc fst₁ , snd₁) {A = A} i≤j (there .B l) =
  subst (λ f → inserts (suc fst₁ , snd₁) G' (B ∷ G) [ f ]= A) (Fin-fst-≡ refl) (there B (inserts-[]=-shifted G G' (fst₁ , pred-≤-pred snd₁) (pred-≤-pred i≤j) l))

_+++_+++_ : forall {m n} -> Context m -> Type -> Context n -> Context (suc (m + n))
[] +++ A +++ G2       = A ∷ G2
(B ∷ G1) +++ A +++ G2 = B ∷ (G1 +++ A +++ G2)

++++++-[]=-unaffected : forall {m n} (G1 : Context m) (G2 : Context n) {A B} {j : Fin (suc (n + m))}
  -> (j<n : toℕ j < n)
  -> (G2 +++ A +++ G1) [ j ]= B
  -> (G2 ++ G1) [ toℕ j , <≤-trans j<n (m , +-comm m n) ]= B
++++++-[]=-unaffected G1 [] j<n l = Empty.rec (¬-<-zero j<n)
++++++-[]=-unaffected G1 (C ∷ G2) j<n (here .C .(G2 +++ _ +++ G1)) = subst (λ f -> (C ∷ (G2 ++ G1)) [ f ]= C) (Fin-fst-≡ refl) (here C (G2 ++ G1))
++++++-[]=-unaffected G1 (C ∷ G2) {B = B} j<n (there .C l) =
  let a = ++++++-[]=-unaffected G1 G2 (pred-≤-pred j<n) l
  in
  subst (λ f -> (C ∷ (G2 ++ G1)) [ f ]= B) (Fin-fst-≡ refl) (there C a)

-- Note that `j` stands for `suc fst₁`.
++++++-[]=-shifted : forall {m n} (G1 : Context m) (G2 : Context n) {A B} {fst₁ : ℕ} {snd₁ : suc (fst₁) < suc (n + m)}
  -> (n<j : n < suc fst₁)
  -> (G2 +++ A +++ G1) [ suc fst₁ , snd₁ ]= B
  -> (G2 ++ G1) [ fst₁ , pred-≤-pred snd₁ ]= B
++++++-[]=-shifted G1 [] n<j (there _ l) = subst (λ f → G1 [ f ]= _) (Fin-fst-≡ refl) l
++++++-[]=-shifted {m} {suc n} G1 (C ∷ G2) n<j (there .C {i = zero , snd₁} l) = Empty.rec (¬-<-zero (pred-≤-pred n<j))
++++++-[]=-shifted {m} {suc n} G1 (C ∷ G2) {B = B} n<j (there .C {i = suc fst₁ , snd₁} l) =
  let a = ++++++-[]=-shifted G1 G2 (pred-≤-pred n<j) l
  in
  subst (λ f → (C ∷ (G2 ++ G1)) [ f ]= B) (Fin-fst-≡ refl) (there C a)

++++++-[]=-hit : forall {m n} (G1 : Context m) (G2 : Context n) {A B} {j : Fin (suc (n + m))}
  -> toℕ j ≡ n
  -> (G2 +++ A +++ G1) [ j ]= B
  -> A ≡ B
++++++-[]=-hit G1 [] j≡n (here _ .G1) = refl
++++++-[]=-hit G1 [] j≡n (there _ l) = Empty.rec (snotz j≡n)
++++++-[]=-hit G1 (C ∷ G2) j≡n (here .C .(G2 +++ _ +++ G1)) = Empty.rec (znots j≡n)
++++++-[]=-hit G1 (C ∷ G2) j≡n (there .C l) = ++++++-[]=-hit G1 G2 (injSuc j≡n) l

infix 2 _<:_

data _<:_ : Type -> Type -> Set where
  S-Refl : forall {A} -> A <: A
  S-Arr : forall {A1 B1 A2 B2} -> A2 <: A1 -> B1 <: B2 -> A1 => B1 <: A2 => B2
  S-Top : forall {A} -> A <: Top

infix 2 _⊢_::_

data _⊢_::_ {n : ℕ} (G : Context n) : Term n -> Type -> Set where
  axiom : forall {i : Fin n} {A}
    -> G [ i ]= A
    -> G ⊢ var i :: A

  =>I : forall {A B : Type} {e : Term (suc n)}
    -> A ∷ G ⊢ e :: B
    -> G ⊢ abs e :: A => B

  =>E : forall {A B : Type} {e1 e2 : Term n}
    -> G ⊢ e1 :: A => B
    -> G ⊢ e2 :: A
    -> G ⊢ e1 · e2 :: B

  sub : forall {A B : Type} {e}
    -> G ⊢ e :: A
    -> A <: B
    -> G ⊢ e :: B

weakening : forall {m n} (i : Fin (suc m)) {G : Context m} (G' : Context n) {e : Term m} {A}
  -> G ⊢ e :: A
  -> inserts i G' G ⊢ shift n i e :: A
weakening {m = m} {n = n} i {G = G} G' {e = var j} (axiom l)
  with toℕ i ≟ toℕ j
... | lt i<j = axiom (inserts-[]=-shifted G G' i (≤-trans (1 , refl) i<j) l)
... | eq i≡j = axiom (inserts-[]=-shifted G G' i (0 , i≡j) l)
... | gt j<i = axiom (inserts-[]=-unaffected G G' i j<i l)
weakening {n = n} i {G = G} G' {e = abs e} {A = A => B} (=>I D) =
  =>I (subst (λ f -> (A ∷ inserts f G' G) ⊢ shift n (fsuc i) e :: B) (Fin-fst-≡ {j = i} refl) (weakening (fsuc i) G' D))
weakening i G' (=>E D D₁) = =>E (weakening i G' D) (weakening i G' D₁)
weakening i G' (sub D s) = sub (weakening i G' D) s

helper3 : forall {n} -> (suc n , ≤-refl) ≡ (suc n , suc-≤-suc ≤-refl)
helper3 = Fin-fst-≡ refl

helper4 : forall m n (j : Fin (suc (n + m))) j<n
  -> (toℕ j , <≤-trans j<n (m , +-comm m n)) ≡ (toℕ j , <≤-trans j<n (pred-≤-pred (≤-trans (0 , refl) (suc-≤-suc (m , +-comm m n)))))
helper4 m n j j<n = Fin-fst-≡ refl

helper5 : forall m n (G1 : Context m) (G2 : Context n)
  -> PathP (λ i -> Context (+-comm n m (~ i))) (subst Context (+-comm n m) (G2 ++ G1)) (G2 ++ G1)
helper5 m n G1 G2 = symP {A = λ i -> Context (+-comm n m i)} (toPathP refl)

helper6 : forall m n (e : Term (m + n))
  -> PathP (λ i -> Term (+-comm m n i)) e (transport (λ i -> Term (+-comm m n i)) e)
helper6 m n e = toPathP refl

helper' : forall m n -> +-comm m n ≡ sym (+-comm n m)
helper' m n = isSetℕ (m + n) (n + m) (+-comm m n) (sym (+-comm n m))

helper7 : forall m n (e : Term (m + n))
  -> PathP (λ i -> Term (+-comm n m (~ i))) e (transport (λ i -> Term (+-comm m n i)) e)
helper7 m n e = subst (λ m+n≡n+m → PathP (λ i → Term (m+n≡n+m i)) e (transport (λ i -> Term (+-comm m n i)) e)) (helper' m n) (helper6 m n e)

substitution : forall {m n} (G1 : Context m) (G2 : Context n) (e1 : Term (suc (n + m))) {e2 : Term m} {A B}
  -> G1 ⊢ e2 :: A
  -> G2 +++ A +++ G1 ⊢ e1 :: B
  -> G2 ++ G1 ⊢ subst′ e2 (n , ≤-refl) e1 :: B
substitution G1 G2 e1 D' (sub D s) = sub (substitution G1 G2 e1 D' D) s
substitution {m} {n} G1 G2 (var j) {e2 = e2} {B = B} D' (axiom l) with toℕ j ≟ toℕ (n , ≤-refl)
... | lt j<n = axiom (transport (λ i -> (G2 ++ G1) [ helper4 m n j j<n i ]= B) (++++++-[]=-unaffected G1 G2 j<n l))
... | eq j≡n = let a = weakening fzero G2 D' in transport (λ i → helper5 m n G1 G2 i ⊢ helper7 m n (shift n fzero e2) i :: ++++++-[]=-hit G1 G2 j≡n l i ) a
... | gt n<j with j
...             | zero , snd₁ = Empty.rec (¬-<-zero n<j)
...             | suc fst₁ , snd₁ = axiom (++++++-[]=-shifted G1 G2 n<j l)
substitution G1 G2 (abs e1) {e2 = e2} D' (=>I {A} {B} D) = =>I (transport (λ i → (A ∷ (G2 ++ G1)) ⊢ subst′ e2 (helper3 i) e1 :: B) (substitution G1 (A ∷ G2) e1 D' D))
substitution G1 G2 (e · e') D' (=>E D D₁) = =>E (substitution G1 G2 e D' D) (substitution G1 G2 e' D' D₁)

S-Trans : forall {A B C}
  -> A <: B
  -> B <: C
  -> A <: C
S-Trans S-Refl s2 = s2
S-Trans (S-Arr s1 s3) S-Refl = S-Arr s1 s3
S-Trans (S-Arr s1 s3) (S-Arr s2 s4) = S-Arr (S-Trans s2 s1) (S-Trans s3 s4)
S-Trans (S-Arr s1 s3) S-Top = S-Top
S-Trans S-Top S-Refl = S-Top
S-Trans S-Top S-Top = S-Top

inversion/S-Arr : forall {A1 B1 A2 B2}
  -> A1 => B1 <: A2 => B2
  -> (A2 <: A1) × (B1 <: B2)
inversion/S-Arr S-Refl = S-Refl , S-Refl
inversion/S-Arr (S-Arr s s₁) = s , s₁

inversion/=>I : forall {n} {G : Context n} {e : Term (suc n)} {A}
  -> G ⊢ abs e :: A
  -> Σ[ B ∈ Type ] Σ[ C ∈ Type ] ((B ∷ G ⊢ e :: C)  ×  (B => C <: A))
inversion/=>I (=>I D) = _ , _ , D , S-Refl
inversion/=>I (sub D s)
  with inversion/=>I D
... | B , C , D' , s' = B , C , D' , S-Trans s' s

preservation : forall {n} {G : Context n} (e : Term n) {e' : Term n} {A}
  -> G ⊢ e :: A
  -> e ▷ e'
  -> G ⊢ e' :: A
preservation e (sub D s) st = sub (preservation e D st) s
preservation (_ · _) (=>E D D₁) (cong/app s) = =>E (preservation _ D s) D₁
preservation {G = G} (abs e1 · e2) (=>E D D₁) beta/=>
  with inversion/=>I D
... | _ , _ , D , s with inversion/S-Arr s
... | sdom , scod = substitution G [] e1 (sub D₁ sdom) (sub D scod)

-- Path.
data P {n : ℕ} : Term n -> Set where
  var : forall {i : Fin n} -> P (var i)
  app : forall {e1 e2 : Term n} -> P e1 -> P (e1 · e2)

data Whnf {n : ℕ} : Term n -> Set where
  `_ : forall {p : Term n} -> P p -> Whnf p
  abs : forall {e : Term (suc n)} -> Whnf (abs e)

progress : forall {n} {G : Context n} {e : Term n} {A}
  -> G ⊢ e :: A
  -> (Σ[ e' ∈ Term n ] e ▷ e') ⊎ Whnf e
progress (axiom x) = inr (` var)
progress (=>I D) = inr abs
progress {e = e1 · e2} (=>E D D₁) with e1 | progress D
... | _      | inl (e1' , s) = inl ((e1' · e2) , cong/app s)
... | _      | inr (` p)     = inr (` app p)
... | abs e1 | inr abs       = inl (subst′ e2 fzero e1 , beta/=>)
progress (sub D _) = progress D
