{-# OPTIONS --cubical --safe #-}
module Subtyping where

open import Cubical.Core.Everything hiding (Type)
open import Cubical.Foundations.Prelude using (refl; sym; symP; cong; _∙_; transport; subst; transportRefl; transport-filler; toPathP; fromPathP; congP)
open import Cubical.Foundations.Transport using (transport⁻Transport)

open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; +-comm; snotz; znots; +-suc; +-zero; injSuc; isSetℕ)
open import Cubical.Data.Nat.Order using (_≟_; lt; eq; gt; ≤-k+; ≤-+k; ≤-trans; pred-≤-pred; _≤_; _<_; ¬m+n<m; ¬-<-zero; suc-≤-suc; <-k+; <-+k; zero-≤; m≤n-isProp; <≤-trans; ≤-refl; <-weaken)
open import Cubical.Data.Fin using (Fin; toℕ; fzero; fsuc; Fin-fst-≡)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd; ΣPathP; Σ-cong-snd)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
import Cubical.Data.Empty as Empty

open import Label using (Label; Record; nil; cons; _∈_; find; l∈r-isProp)

-- A term with at most `n` free variables.
data Term (n : ℕ) : Set where
  var : Fin n -> Term n
  abs : Term (suc n) -> Term n
  _·_ : Term n -> Term n -> Term n
  rec : forall {l} -> Record (Term n) l -> Term n
  _#_ : Term n -> Label -> Term n

shift : forall {m : ℕ} (n : ℕ) (i : Fin (suc m)) (e : Term m) -> Term (m + n)
shiftRecord : forall {m : ℕ} (n : ℕ) (i : Fin (suc m)) {l : Label} (r : Record (Term m) l) -> Record (Term (m + n)) l

shift {m} n i (var j)
  with toℕ i ≟ toℕ j
... | lt _ = var (toℕ j + n , ≤-+k (snd j))
... | eq _ = var (toℕ j + n , ≤-+k (snd j))
... | gt _ = var (toℕ j , ≤-trans (snd j) (n , +-comm n m))
shift n i (abs e) = abs (shift n (fsuc i) e)
shift n i (e · e₁) = shift n i e · shift n i e₁
shift n i (rec r) = rec (shiftRecord n i r)
shift n i (e # l) = shift n i e # l

shiftRecord n i nil = nil
shiftRecord n i (cons r l' x x₁) = cons (shiftRecord n i r) l' (shift n i x) x₁

subst′ : forall {m n : ℕ}
  -> (e' : Term m)
  -> (i : Fin (suc n))
  -> (e1 : Term (suc (n + m)))
  -> Term (n + m)
substRecord : forall {m n : ℕ}
  -> (e' : Term m)
  -> (i : Fin (suc n))
  -> forall {l : Label}
  -> (r1 : Record (Term (suc (n + m))) l)
  -> Record (Term (n + m)) l

subst′ {m} {n} e' i (var j) with toℕ j ≟ toℕ i
... | lt j<i = var (toℕ j , <≤-trans j<i (pred-≤-pred (≤-trans (snd i) (suc-≤-suc (m , +-comm m n)))))
... | eq _ = transport (λ i₁ → Term (+-comm m n i₁)) (shift n fzero e')
... | gt i<j with j
...             | zero , _        = Empty.rec (¬-<-zero i<j)
...             | suc fst₁ , snd₁ = var (fst₁ , pred-≤-pred snd₁)
subst′ e' i (abs e1) = abs (subst′ e' (fsuc i) e1)
subst′ e' i (e1 · e2) = subst′ e' i e1 · subst′ e' i e2
subst′ e' i (rec r) = rec (substRecord e' i r)
subst′ e' i (e # l) = subst′ e' i e # l

substRecord e' i nil = nil
substRecord e' i (cons r1 l' x x₁) = cons (substRecord e' i r1) l' (subst′ e' i x) x₁

infix 3 _▷_

data _▷_ {n : ℕ} : Term n -> Term n -> Set where
  beta/=> : forall {e1 : Term (suc n)} {e2 : Term n} -> abs e1 · e2 ▷ subst′ e2 fzero e1
  cong/app : forall {e1 e1' e2 : Term n} -> e1 ▷ e1' -> e1 · e2 ▷ e1' · e2

  beta/rec : forall {l'} {r : Record (Term n) l'} {l} {l∈r : l ∈ r} -> rec r # l ▷ find l r l∈r
  cong/# : forall {e e' : Term n} {l} -> e ▷ e' -> e # l  ▷ e' # l

data Base : Set where
  Unit : Base
  Int : Base

infixr 8 _=>_

data Type : Set where
  base : Base -> Type
  Top : Type
  _=>_ : Type -> Type -> Type
  rec : forall {l} -> Record Type l -> Type

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
infix 2 _<::_

data _<:_ : Type -> Type -> Set
data _<::_ {l1 l2 : Label} : Record Type l1 -> Record Type l2 -> Set

data _<:_ where
  S-Refl : forall {A} -> A <: A
  S-Arr : forall {A1 B1 A2 B2} -> A2 <: A1 -> B1 <: B2 -> A1 => B1 <: A2 => B2
  S-Top : forall {A} -> A <: Top
  S-Record : forall {l1 l2} {r1 : Record Type l1} {r2 : Record Type l2} -> r1 <:: r2 -> rec r1 <: rec r2

data _<::_ {l1} {l2} where
  S-nil : l2 ≤ l1 -> nil <:: nil

  S-cons1 : forall {l1'} {r1 : Record Type l1'} {r2 : Record Type l2} {A} {l1'<l1 : l1' < l1}
    -> r1 <:: r2
    -> cons r1 l1 A l1'<l1 <:: r2

  S-cons2 : forall {l1' l2'} {r1 : Record Type l1'} {r2 : Record Type l2'} {A B} {l1'<l1 : l1' < l1} .{l2'<l2 : l2' < l2}
    -> r1 <:: r2
    -> A <: B
    -> l1 ≡ l2
    -> cons r1 l1 A l1'<l1 <:: cons r2 l2 B l2'<l2

<::-implies-≥ : forall {l1 l2} {r1 : Record Type l1} {r2 : Record Type l2} -> r1 <:: r2 -> l2 ≤ l1
<::-implies-≥ (S-nil x) = x
<::-implies-≥ (S-cons1 {l1'<l1 = l1'<l1} s) = ≤-trans (<::-implies-≥ s) (<-weaken l1'<l1)
<::-implies-≥ (S-cons2 s x x₁) = 0 , sym x₁

helper/<::-∈ : forall {l1 l2} {r1 : Record Type l1} {r2 : Record Type l2}
  -> r1 <:: r2
  -> forall {l}
  -> l ∈ r2
  -> l ∈ r1
helper/<::-∈ (S-cons1 {l1'<l1 = l1'<l1} s) l∈r2 = _∈_.there {lt = l1'<l1} (helper/<::-∈ s l∈r2)
helper/<::-∈ (S-cons2 {r1 = r1} {A = A} {l1'<l1 = l1'<l1} _ x l1≡l2) (_∈_.here {lt = a} e) = transport (λ i -> (l1≡l2 ∙ sym e) i ∈ cons r1 _ A l1'<l1) (_∈_.here {lt = l1'<l1} refl)
helper/<::-∈ (S-cons2 {l1'<l1 = l1'<l1} s x l1≡l2) (_∈_.there l∈r2) = _∈_.there {lt = l1'<l1} (helper/<::-∈ s l∈r2)

infix 2 _⊢_::_
infix 2 _⊢_:::_

data _⊢_::_ {n : ℕ} (G : Context n) : Term n -> Type -> Set
data _⊢_:::_ {n : ℕ} (G : Context n) {l} : Record (Term n) l -> Record Type l -> Set

data _⊢_::_ {n} G where
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

  recI : forall {l} {r : Record (Term n) l} {rt : Record Type l}
    -> G ⊢ r ::: rt
    -> G ⊢ rec r :: rec rt

  recE : forall {l'} {r : Record Type l'} {e : Term n} {l : Label}
    -> G ⊢ e :: rec r
    -> (l∈r : l ∈ r)
    -> G ⊢ e # l :: find l r l∈r

  sub : forall {A B : Type} {e}
    -> G ⊢ e :: A
    -> A <: B
    -> G ⊢ e :: B

data _⊢_:::_ {n} G {l} where
  rec/nil : G ⊢ nil ::: nil

  rec/cons : forall {l'} {r : Record (Term n) l'} {rt : Record Type l'} {e A} .{l'<l : (l' < l)}
    -> G ⊢ r ::: rt
    -> G ⊢ e :: A
    -> G ⊢ cons r l e l'<l ::: cons rt l A l'<l

helper/∈ : forall {n} {G : Context n} {l} {r : Record (Term n) l} {rt : Record Type l}
  -> G ⊢ r ::: rt
  -> forall {l₁}
  -> l₁ ∈ r
  -> l₁ ∈ rt
helper/∈ (rec/cons D x) (_∈_.here {lt = y} e) = _∈_.here {lt = y} e
helper/∈ (rec/cons D x) (_∈_.there {lt = y} l₁∈r) = _∈_.there {lt = y} (helper/∈ D l₁∈r)

helper/∈′ : forall {n} {G : Context n} {l} {r : Record (Term n) l} {rt : Record Type l}
  -> G ⊢ r ::: rt
  -> forall {l₁}
  -> l₁ ∈ rt
  -> l₁ ∈ r
helper/∈′ (rec/cons D x) (_∈_.here {lt = y} e) = _∈_.here {lt = y} e
helper/∈′ (rec/cons D x) (_∈_.there {lt = y} l₁∈r) = _∈_.there {lt = y} (helper/∈′ D l₁∈r)

weakening : forall {m n} (i : Fin (suc m)) {G : Context m} (G' : Context n) {e : Term m} {A}
  -> G ⊢ e :: A
  -> inserts i G' G ⊢ shift n i e :: A
weakeningRecord : forall {m n} (i : Fin (suc m)) {G : Context m} (G' : Context n) {l} {r : Record (Term m) l} {rt}
  -> G ⊢ r ::: rt
  -> inserts i G' G ⊢ shiftRecord n i r ::: rt

weakening {m = m} {n = n} i {G = G} G' {e = var j} (axiom l)
  with toℕ i ≟ toℕ j
... | lt i<j = axiom (inserts-[]=-shifted G G' i (≤-trans (1 , refl) i<j) l)
... | eq i≡j = axiom (inserts-[]=-shifted G G' i (0 , i≡j) l)
... | gt j<i = axiom (inserts-[]=-unaffected G G' i j<i l)
weakening {n = n} i {G = G} G' {e = abs e} {A = A => B} (=>I D) =
  =>I (subst (λ f -> (A ∷ inserts f G' G) ⊢ shift n (fsuc i) e :: B) (Fin-fst-≡ {j = i} refl) (weakening (fsuc i) G' D))
weakening i G' (=>E D D₁) = =>E (weakening i G' D) (weakening i G' D₁)
weakening i G' (sub D s) = sub (weakening i G' D) s
weakening i G' (recI D) = recI (weakeningRecord i G' D)
weakening i G' (recE D l∈r) = recE (weakening i G' D) l∈r

weakeningRecord i G' rec/nil = rec/nil
weakeningRecord i G' (rec/cons x x₁) = rec/cons (weakeningRecord i G' x) (weakening i G' x₁)

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
substitutionRecord : forall {m n} (G1 : Context m) (G2 : Context n) {l} (r : Record (Term (suc (n + m))) l) {e2 : Term m} {A} {rt}
  -> G1 ⊢ e2 :: A
  -> G2 +++ A +++ G1 ⊢ r ::: rt
  -> G2 ++ G1 ⊢ substRecord e2 (n , ≤-refl) r ::: rt

substitution G1 G2 e1 D' (sub D s) = sub (substitution G1 G2 e1 D' D) s
substitution {m} {n} G1 G2 (var j) {e2 = e2} {B = B} D' (axiom l) with toℕ j ≟ toℕ (n , ≤-refl)
... | lt j<n = axiom (transport (λ i -> (G2 ++ G1) [ helper4 m n j j<n i ]= B) (++++++-[]=-unaffected G1 G2 j<n l))
... | eq j≡n = let a = weakening fzero G2 D' in transport (λ i → helper5 m n G1 G2 i ⊢ helper7 m n (shift n fzero e2) i :: ++++++-[]=-hit G1 G2 j≡n l i ) a
... | gt n<j with j
...             | zero , snd₁ = Empty.rec (¬-<-zero n<j)
...             | suc fst₁ , snd₁ = axiom (++++++-[]=-shifted G1 G2 n<j l)
substitution G1 G2 (abs e1) {e2 = e2} D' (=>I {A} {B} D) = =>I (transport (λ i → (A ∷ (G2 ++ G1)) ⊢ subst′ e2 (helper3 i) e1 :: B) (substitution G1 (A ∷ G2) e1 D' D))
substitution G1 G2 (e · e') D' (=>E D D₁) = =>E (substitution G1 G2 e D' D) (substitution G1 G2 e' D' D₁)
substitution G1 G2 (rec r) D' (recI D) = recI (substitutionRecord G1 G2 r D' D)
substitution G1 G2 (e # l) D' (recE D l∈r) = recE (substitution G1 G2 e D' D) l∈r

substitutionRecord G1 G2 nil D' rec/nil = rec/nil
substitutionRecord G1 G2 (cons r l e _) D' (rec/cons D x) = rec/cons (substitutionRecord G1 G2 r D' D) (substitution G1 G2 e D' x)

S-Trans : forall {A B C}
  -> A <: B
  -> B <: C
  -> A <: C
S-TransRecord : forall {l1 l2 l3} {r1 : Record Type l1} {r2 : Record Type l2} {r3 : Record Type l3}
  -> r1 <:: r2
  -> r2 <:: r3
  -> r1 <:: r3

S-Trans S-Refl s2 = s2
S-Trans (S-Arr s1 s3) S-Refl = S-Arr s1 s3
S-Trans (S-Arr s1 s3) (S-Arr s2 s4) = S-Arr (S-Trans s2 s1) (S-Trans s3 s4)
S-Trans (S-Arr s1 s3) S-Top = S-Top
S-Trans S-Top S-Refl = S-Top
S-Trans S-Top S-Top = S-Top
S-Trans (S-Record s1) S-Refl = S-Record s1
S-Trans (S-Record s1) S-Top = S-Top
S-Trans (S-Record s1) (S-Record s2) = S-Record (S-TransRecord s1 s2)

S-TransRecord (S-nil x) (S-nil y) = S-nil (≤-trans y x)
S-TransRecord (S-cons1 {l1'<l1 = l1'<l1} x) x₁ = S-cons1 {l1'<l1 = l1'<l1} (S-TransRecord x x₁)
S-TransRecord (S-cons2 {l1'<l1 = a} x x₂ _) (S-cons1 x₁) = S-cons1 {l1'<l1 = a} (S-TransRecord x x₁)
S-TransRecord (S-cons2 {l1'<l1 = a} x x₂ l1≡l2) (S-cons2 x₁ x₃ l2≡l3) = S-cons2 {l1'<l1 = a} (S-TransRecord x x₁) (S-Trans x₂ x₃) (l1≡l2 ∙ l2≡l3)

inversion/S-Arr : forall {A1 B1 A2 B2}
  -> A1 => B1 <: A2 => B2
  -> (A2 <: A1) × (B1 <: B2)
inversion/S-Arr S-Refl = S-Refl , S-Refl
inversion/S-Arr (S-Arr s s₁) = s , s₁

helper/inversion/S-Record : forall {l1 l2} {r1 : Record Type l1} {r2 : Record Type l2}
  -> (s : r1 <:: r2)
  -> forall {l}
  -> (l∈r2 : l ∈ r2)
  -> find l r1 (helper/<::-∈ s l∈r2) <: find l r2 l∈r2
helper/inversion/S-Record (S-cons1 s) l∈r2 = helper/inversion/S-Record s l∈r2
helper/inversion/S-Record {l1} {r1 = cons r1 l1 A k} (S-cons2 {B = B} {l1'<l1 = l1'<l1} _ x l1≡l2) {l = l} (_∈_.here {lt = u} e) =
  subst (λ z -> find l (cons r1 l1 A k) z <: B) (l∈r-isProp l (cons r1 l1 A k) (_∈_.here {lt = l1'<l1} (e ∙ sym l1≡l2)) (transport (λ i → (l1≡l2 ∙ sym e) i ∈ cons r1 l1 A k) (_∈_.here refl))) x
helper/inversion/S-Record (S-cons2 s x x₁) (_∈_.there l∈r2) = helper/inversion/S-Record s l∈r2

inversion/S-Record : forall {l1 l2} {r1 : Record Type l1} {r2 : Record Type l2}
  -> rec r1 <: rec r2
  -> forall {l} (l∈r2 : l ∈ r2) -> Σ[ l∈r1 ∈ (l ∈ r1) ] (find l r1 l∈r1 <: find l r2 l∈r2)
inversion/S-Record S-Refl l∈r2 = l∈r2 , S-Refl
inversion/S-Record (S-Record s) l∈r2 = helper/<::-∈ s l∈r2 , helper/inversion/S-Record s l∈r2

inversion/=>I : forall {n} {G : Context n} {e : Term (suc n)} {A}
  -> G ⊢ abs e :: A
  -> Σ[ B ∈ Type ] Σ[ C ∈ Type ] ((B ∷ G ⊢ e :: C)  ×  (B => C <: A))
inversion/=>I (=>I D) = _ , _ , D , S-Refl
inversion/=>I (sub D s)
  with inversion/=>I D
... | B , C , D' , s' = B , C , D' , S-Trans s' s

helper/inversion/recI : forall {n} {G : Context n} {l} {r : Record (Term n) l} {rt : Record Type l}
  -> (D : G ⊢ r ::: rt)
  -> forall {l₁}
  -> (l₁∈r : l₁ ∈ r)
  -> G ⊢ find l₁ r l₁∈r :: find l₁ rt (helper/∈ D l₁∈r)
helper/inversion/recI (rec/cons D x) (_∈_.here e) = x
helper/inversion/recI (rec/cons D x) (_∈_.there l₁∈r) = helper/inversion/recI D l₁∈r

inversion/recI : forall {n} {G : Context n} {l} {r : Record (Term n) l} {A}
  -> G ⊢ rec r :: A
  -> Σ[ rt ∈ Record Type l ] Σ[ f ∈ (forall {l₁} -> l₁ ∈ r -> l₁ ∈ rt) ] Σ[ g ∈ (forall {l₁} -> l₁ ∈ rt -> l₁ ∈ r) ] ((forall {l₁} (l₁∈r : l₁ ∈ r) -> (G ⊢ find l₁ r l₁∈r :: find l₁ rt (f l₁∈r)))  ×  (rec rt <: A))
inversion/recI (recI D) = _ , helper/∈ D , helper/∈′ D , (helper/inversion/recI D) , S-Refl
inversion/recI (sub D s)
  with inversion/recI D
... | rt , f , g , x , s' = rt , f , g , x , S-Trans s' s

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
preservation (e # l) (recE D l∈r) (cong/# s) = recE (preservation e D s) l∈r
preservation {G = G} (rec r # l) (recE D l∈r) (beta/rec {l∈r = l∈r′})
  with inversion/recI D
...  | rt , f , _ , x , s with inversion/S-Record s
...  | sr = let a = x l∈r′ in let l∈rt , b = sr l∈r in sub (subst (λ z -> G ⊢ find l r l∈r′ :: find l rt z) (l∈r-isProp l rt (f l∈r′) (l∈rt)) a) b

-- Path.
data P {n : ℕ} : Term n -> Set where
  var : forall {i : Fin n} -> P (var i)
  app : forall {e1 e2 : Term n} -> P e1 -> P (e1 · e2)
  proj : forall {e} {l} -> P e -> P (e # l)

data Whnf {n : ℕ} : Term n -> Set where
  `_ : forall {p : Term n} -> P p -> Whnf p
  abs : forall {e : Term (suc n)} -> Whnf (abs e)
  rec : forall {l} {r : Record (Term n) l} -> Whnf (rec r)

=>Whnf : forall {n} {G : Context n} {e : Term n} {A B : Type}
  -> G ⊢ e :: A => B
  -> Whnf e
  -> P e ⊎ (Σ[ e' ∈ Term (suc n) ] e ≡ abs e')
=>Whnf {e = var x} D (` x₁) = inl x₁
=>Whnf {e = abs e} D abs = inr (e , refl)
=>Whnf {e = e · e₁} D (` x) = inl x
=>Whnf {e = rec x} D w
  with inversion/recI D
... | ()
=>Whnf {e = e # x} D (` x₁) = inl x₁

recWhnf : forall {n} {G : Context n} {e : Term n} {l} {rt : Record Type l}
  -> G ⊢ e :: rec rt
  -> Whnf e
  -> P e ⊎ (Σ[ l' ∈ Label ] Σ[ r ∈ Record (Term n) l' ] e ≡ rec r)
recWhnf {e = var x} D (` x₁) = inl x₁
recWhnf {e = abs e} D w
  with inversion/=>I D
... | ()
recWhnf {e = e · e₁} D (` x) = inl x
recWhnf {e = rec x} D rec = inr (_ , x , refl)
recWhnf {e = e # x} D (` x₁) = inl x₁

helper/progress : forall {n} {G : Context n} {l1 l2} {r : Record _ l1} {rt : Record _ l2}
  -> G ⊢ rec r :: rec rt
  -> forall {l}
  -> l ∈ rt
  -> l ∈ r
helper/progress D l∈rt
  with inversion/recI D
... | rt0 , f , g , x , s with inversion/S-Record s l∈rt
... | l∈rt0 , s' = g l∈rt0

progress : forall {n} {G : Context n} {e : Term n} {A}
  -> G ⊢ e :: A
  -> (Σ[ e' ∈ Term n ] e ▷ e') ⊎ Whnf e
progress (axiom x) = inr (` var)
progress (=>I D) = inr abs
progress {n} {e = e1 · e2} (=>E D D₁) with progress D
... | inl (e1' , s) = inl ((e1' · e2) , cong/app s)
... | inr w with =>Whnf D w
... | inl p = inr (` app p)
... | inr (e1 , x) = inl (transport (Σ-cong-snd λ x₁ i → (x (~ i) · e2) ▷ x₁) (subst′ e2 fzero e1 , beta/=>))
progress (sub D _) = progress D
progress (recI D) = inr rec
progress {G = G} {e = e # l} (recE D l∈r) with progress D
... | inl (e' , s) = inl ((e' # l) , cong/# s)
... | inr w with recWhnf D w
... | inl p = inr (` proj p)
... | inr (l' , r , x) = inl (transport (Σ-cong-snd λ x₁ i → x (~ i) # l ▷ x₁) (find l r (helper/progress (subst (λ x₁ → G ⊢ x₁ :: _) x D) l∈r) , beta/rec))
