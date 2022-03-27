module Syntax where

open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Bool.Base as Bool using (Bool; false; true; if_then_else_)
open import Data.String.Base using (String)
open import Data.Product
open import Data.List.Base using (List; []; _∷_)
import Data.List.Relation.Unary.First as First
open import Data.List.Relation.Unary.All
open import Function.Base
open import Relation.Binary.PropositionalEquality.Core

-- Terms and types

infixl 10 _∙_

Lv = ℕ
data Term : Set
data Type : Set

data Type where
  -- Universes
  U : Lv → Type
  T : Lv → Term → Type
  -- Π type
  Π : Type → Type → Type

data Term where
  -- Universes
  u : Lv → Term
  t : Lv → Term → Term
  π : Lv → Term → Term → Term
  -- Π type
  ƛ : Term → Term
  _∙_ : Term → Term → Term
  -- variable
  v : ℕ → Term

-- Context

Ctx : Set
Ctx = List Type

-- Variables

private
  variable
    Γ : Ctx
    ℓ : Lv
    L L′ M M′ N N′ A A′ B B′ : Term
    𝔸 𝔸′ 𝔹 𝔹′ ℂ ℂ′ : Type
    x x′ y y′ : ℕ
    s : Bool

-- Weakening and substitutions

infixr 5 ↑_ ⇑_ _∷_
infix 15 _[_] _⟦_⟧

data Subst′ : Bool → Set where
  I   : Subst′ s
  ↑_  : Subst′ s → Subst′ s
  ⇑_  : Subst′ s → Subst′ s
  _∷_ : Term → Subst′ true → Subst′ true

Wk    = Subst′ false
Subst = Subst′ true

wkVar : Wk → ℕ → ℕ
wkVar I     x       = x
wkVar (↑ ρ) x       = suc (wkVar ρ x)
wkVar (⇑ ρ) zero    = zero
wkVar (⇑ ρ) (suc x) = suc (wkVar ρ x)

wk : Wk → Term → Term
wk ρ (u ℓ)     = u ℓ
wk ρ (t ℓ A)   = t ℓ (wk ρ A)
wk ρ (π ℓ A B) = π ℓ (wk ρ A) (wk (⇑ ρ) B)
wk ρ (ƛ M)     = ƛ (wk (⇑ ρ) M)
wk ρ (M ∙ N)   = wk ρ M ∙ wk ρ N
wk ρ (v x)     = v (wkVar ρ x)

substVar : Subst → ℕ → Term
substVar I       x       = v x
substVar (↑ σ)   x       = wk (↑ I) (substVar σ x)
substVar (⇑ σ)   zero    = v zero
substVar (⇑ σ)   (suc x) = wk (↑ I) (substVar σ x)
substVar (M ∷ σ) zero    = M
substVar (M ∷ σ) (suc x) = substVar σ x

_[_] : Term → Subst → Term
u ℓ     [ σ ] = u ℓ
t ℓ A   [ σ ] = t ℓ (A [ σ ])
π ℓ A B [ σ ] = π ℓ (A [ σ ]) (B [ ⇑ σ ])
ƛ M     [ σ ] = ƛ (M [ ⇑ σ ])
(M ∙ N) [ σ ] = M [ σ ] ∙ N [ σ ]
v x     [ σ ] = substVar σ x

_⟦_⟧ : Type → Subst → Type
U ℓ   ⟦ σ ⟧ = U ℓ
T ℓ A ⟦ σ ⟧ = T ℓ (A [ σ ])
Π 𝔸 𝔹 ⟦ σ ⟧ = Π (𝔸 ⟦ σ ⟧) (𝔹 ⟦ ⇑ σ ⟧)

-- Judgements

infix 4 ⊢_ _∶_∈_ _⊢_≈_type _⊢_≈_∶_ _⊢_type _⊢_∶_

data ⊢_ : Ctx → Set
data _∶_∈_ : ℕ → Type → Ctx → Set
data _⊢_≈_type (Γ : Ctx) : Type → Type → Set
data _⊢_≈_∶_ (Γ : Ctx) : Term → Term → Type → Set
_⊢_type : Ctx → Type → Set
_⊢_∶_ : Ctx → Term → Type → Set

Γ ⊢ A type = Γ ⊢ A ≈ A type
Γ ⊢ M ∶ A = Γ ⊢ M ≈ M ∶ A

data ⊢_ where
  ⊢[] : ⊢ []
  _∷_ : Γ ⊢ 𝔸 type → ⊢ Γ → ⊢ 𝔸 ∷ Γ

data _∶_∈_ where
  ∈-zero : zero ∶ 𝔸 ⟦ ↑ I ⟧ ∈ 𝔸 ∷ Γ
  ∈-suc : x ∶ 𝔸 ∈ Γ → suc x ∶ 𝔸 ⟦ ↑ I ⟧ ∈ 𝔹 ∷ Γ

data _⊢_≈_type Γ where

  ≈type-U : ⊢ Γ →
            Γ ⊢ U ℓ ≈ U ℓ type

  ≈type-T : Γ ⊢ A ≈ A′ ∶ U ℓ →
            Γ ⊢ T ℓ A ≈ T ℓ A′ type

  ≈type-Π : Γ ⊢ 𝔸 ≈ 𝔸′ type →
            𝔸 ∷ Γ ⊢ 𝔹 ≈ 𝔹′ type →
            Γ ⊢ Π 𝔸 𝔹 ≈ Π 𝔸′ 𝔹′ type

  ≈type-βTu : ⊢ Γ →
              Γ ⊢ T (suc ℓ) (u ℓ) ≈ U ℓ type

  ≈type-βTt : Γ ⊢ A ∶ U ℓ →
              Γ ⊢ T (suc ℓ) (t ℓ A) ≈ T ℓ A type

  ≈type-βTπ : Γ ⊢ A ∶ U ℓ →
              T ℓ A ∷ Γ ⊢ B ∶ U ℓ →
              Γ ⊢ T ℓ (π ℓ A B) ≈ Π (T ℓ A) (T ℓ B) type

  ≈type-sym : Γ ⊢ 𝔸 ≈ 𝔹 type →
              Γ ⊢ 𝔹 ≈ 𝔸 type

  ≈type-trans : Γ ⊢ 𝔸 ≈ 𝔹 type →
                Γ ⊢ 𝔹 ≈ ℂ type →
                Γ ⊢ 𝔸 ≈ ℂ type

data _⊢_≈_∶_ Γ where

  ≈-u : ⊢ Γ →
        Γ ⊢ u ℓ ≈ u ℓ ∶ U (suc ℓ)

  ≈-t : Γ ⊢ A ≈ A′ ∶ U ℓ →
        Γ ⊢ t ℓ A ≈ t ℓ A′ ∶ U (suc ℓ)

  ≈-π : Γ ⊢ A ≈ A′ ∶ U ℓ →
        T ℓ A ∷ Γ ⊢ B ≈ B′ ∶ U ℓ →
        Γ ⊢ π ℓ A B ≈ π ℓ A′ B′ ∶ U ℓ

  ≈-ƛ : 𝔸 ∷ Γ ⊢ M ≈ M′ ∶ 𝔹 →
        Γ ⊢ ƛ M ≈ ƛ M′ ∶ Π 𝔸 𝔹

  ≈-∙ : Γ ⊢ M ≈ M′ ∶ Π 𝔸 𝔹 →
        Γ ⊢ N ≈ N′ ∶ 𝔸 →
        Γ ⊢ M ∙ N ≈ M′ ∙ N′ ∶ 𝔹 ⟦ N ∷ I ⟧

  ≈-v : ⊢ Γ →
        x ∶ 𝔸 ∈ Γ →
        Γ ⊢ v x ≈ v x ∶ 𝔸

  ≈-β : 𝔸 ∷ Γ ⊢ M ∶ 𝔹 →
        Γ ⊢ N ∶ 𝔸 →
        Γ ⊢ ƛ M ∙ N ≈ M [ N ∷ I ] ∶ 𝔹 ⟦ N ∷ I ⟧

  ≈-η : Γ ⊢ M ∶ Π 𝔸 𝔹 →
        Γ ⊢ M ≈ ƛ (M [ ↑ I ] ∙ v 0) ∶ Π 𝔸 𝔹

  ≈-sym : Γ ⊢ M ≈ N ∶ 𝔸 →
          Γ ⊢ N ≈ M  ∶ 𝔸

  ≈-trans : Γ ⊢ L ≈ M ∶ 𝔸 →
            Γ ⊢ M ≈ N ∶ 𝔸 →
            Γ ⊢ L ≈ N ∶ 𝔸

  ≈-conv : Γ ⊢ 𝔸 ≈ 𝔹 type →
           Γ ⊢ M ≈ N ∶ 𝔸 →
           Γ ⊢ M ≈ N ∶ 𝔹

-- Lemmas about judgements

ctx-hd : ⊢ 𝔸 ∷ Γ → Γ ⊢ 𝔸 type
ctx-hd (J ∷ _) = J

ctx-tl : ⊢ 𝔸 ∷ Γ → ⊢ Γ
ctx-tl (_ ∷ J) = J

type⇒ctx : Γ ⊢ 𝔸 ≈ 𝔸′ type → ⊢ Γ
true⇒ctx : Γ ⊢ M ≈ M′ ∶ 𝔸 → ⊢ Γ

type⇒ctx (≈type-U ⊢Γ) = ⊢Γ
type⇒ctx (≈type-T J) = true⇒ctx J
type⇒ctx (≈type-Π J _) = type⇒ctx J
type⇒ctx (≈type-βTu ⊢Γ) = ⊢Γ
type⇒ctx (≈type-βTt J) = true⇒ctx J
type⇒ctx (≈type-βTπ J _) = true⇒ctx J
type⇒ctx (≈type-sym J) = type⇒ctx J
type⇒ctx (≈type-trans J _) = type⇒ctx J

true⇒ctx (≈-u ⊢Γ) = ⊢Γ
true⇒ctx (≈-t J) = true⇒ctx J
true⇒ctx (≈-π J _) = true⇒ctx J
true⇒ctx (≈-ƛ J) = ctx-tl (true⇒ctx J)
true⇒ctx (≈-∙ J _) = true⇒ctx J
true⇒ctx (≈-v ⊢Γ _) = ⊢Γ
true⇒ctx (≈-β _ J) = true⇒ctx J
true⇒ctx (≈-η J) = true⇒ctx J
true⇒ctx (≈-sym J) = true⇒ctx J
true⇒ctx (≈-trans J _) = true⇒ctx J
true⇒ctx (≈-conv J _) = type⇒ctx J

module ≈type-Reasoning where

  infix 1 begin[_]_
  infixr 2 _≈type⟨_⟩_ ≈type-∎

  begin[_]_ : ∀ Γ → Γ ⊢ 𝔸 ≈ 𝔹 type → Γ ⊢ 𝔸 ≈ 𝔹 type
  begin[ Γ ] p = p

  _≈type⟨_⟩_ : ∀ 𝔸 → Γ ⊢ 𝔸 ≈ 𝔹 type → Γ ⊢ 𝔹 ≈ ℂ type → Γ ⊢ 𝔸 ≈ ℂ type
  𝔸 ≈type⟨ p ⟩ q = ≈type-trans p q

  ≈type-∎ : ∀ 𝔸 𝔹 → Γ ⊢ 𝔸 ≈ 𝔹 type → Γ ⊢ 𝔸 ≈ 𝔹 type
  ≈type-∎ _ _ p = p

  syntax ≈type-∎ 𝔸 𝔹 p = 𝔸 ≈type[ p ] 𝔹

⊢U : [] ⊢ U ℓ type
⊢U = ≈type-U ⊢[]

⊢Tu : [] ⊢ T (suc ℓ) (u ℓ) type
⊢Tu = ≈type-T (≈-u ⊢[])

⊢id : Γ ⊢ 𝔸 type → Γ ⊢ ƛ (v 0) ∶ Π 𝔸 (𝔸 ⟦ ↑ I ⟧)
⊢id J = ≈-ƛ (≈-v (J ∷ type⇒ctx J) ∈-zero)

⊢Πx,x : [] ⊢ T (suc ℓ) (π (suc ℓ) (u ℓ) (t ℓ (v 0))) ≈ Π (U ℓ) (T ℓ (v 0)) type
⊢Πx,x {ℓ = ℓ} = begin[ [] ]
  T (suc ℓ) (π (suc ℓ) (u ℓ) (t ℓ (v 0)))     ≈type⟨ ≈type-βTπ (≈-u ⊢[]) (≈-t J₂) ⟩
  Π (T (suc ℓ) (u ℓ)) (T (suc ℓ) (t ℓ (v 0))) ≈type[ ≈type-Π (≈type-βTu ⊢[]) (≈type-βTt J₂) ]
  Π (U ℓ) (T ℓ (v 0))
  where
    open ≈type-Reasoning

    J₁ : ⊢ T (suc ℓ) (u ℓ) ∷ []
    J₁ = ≈type-T (≈-u ⊢[]) ∷ ⊢[]

    J₂ : T (suc ℓ) (u ℓ) ∷ [] ⊢ v 0 ∶ U ℓ
    J₂ = ≈-conv (≈type-βTu J₁) (≈-v J₁ ∈-zero)
