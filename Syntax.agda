module Syntax where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.String.Base using (String)
open import Data.Product
open import Data.List.Base
open import Data.List.Relation.Unary.First
open import Data.List.Relation.Unary.All
open import Function.Base
open import Relation.Binary.PropositionalEquality.Core

Id = String × ℕ
Lv = ℕ

data Term : Set
data Type : Set

data Type where
  -- Universes
  U : Lv → Type
  T : Lv → Term → Type
  -- Π type
  Π : Id → Type → Type → Type

infixl 10 _∙_

data Term where
  -- Universes
  u : Lv → Term
  t : Lv → Term → Term
  -- Π type
  π : Lv → Id → Term → Term → Term
  ƛ : Id → Type → Term → Term
  _∙_ : Term → Term → Term
  -- variable
  v : Id → Term

Ctx : Set
Ctx = List (Id × Type)

infix 4 _∶_∈_ ⊢_ _⊢_≈_type _⊢_≈_∶_ _⊢_type _⊢_∶_

_∶_∈_ : Id → Type → Ctx → Set
x ∶ A ∈ Γ = First ((_≢ x) ∘ proj₁) (λ (x′ , A′) → x ≡ x′ × A ≡ A′) Γ

data ⊢_ : Ctx → Set
data _⊢_≈_type (Γ : Ctx) : Type → Type → Set
data _⊢_≈_∶_ (Γ : Ctx) : Term → Term → Type → Set

_⊢_type : Ctx → Type → Set
Γ ⊢ A type = Γ ⊢ A ≈ A type

_⊢_∶_ : Ctx → Term → Type → Set
Γ ⊢ M ∶ A = Γ ⊢ M ≈ M ∶ A

private
  variable
    Γ : Ctx
    ℓ : Lv
    M M′ M″ N N′ A A′ B B′ : Term
    𝔸 𝔸′ 𝔸″ 𝔹 𝔹′ ℂ ℂ′ : Type
    x x′ y y′ : Id

data ⊢_ where
  ⊢[] : ⊢ []
  ⊢∷ : ⊢ Γ → Γ ⊢ 𝔸 type → ⊢ (x , 𝔸) ∷ Γ

data _⊢_≈_type Γ where
  ≈type-U : ⊢ Γ →
            Γ ⊢ U ℓ ≈ U ℓ type

  ≈type-T : Γ ⊢ A ≈ A′ ∶ U ℓ →
            Γ ⊢ T ℓ A ≈ T ℓ A′ type

  ≈type-Π : Γ ⊢ 𝔸 ≈ 𝔸′ type →
            (x , 𝔸) ∷ Γ ⊢ 𝔹 ≈ 𝔹′ type →
            Γ ⊢ Π x 𝔸 𝔹 ≈ Π x 𝔸′ 𝔹′ type

  ≈type-βTu : ⊢ Γ →
              Γ ⊢ T (suc ℓ) (u ℓ) ≈ U ℓ type

  ≈type-βTt : Γ ⊢ A ∶ U ℓ →
              Γ ⊢ T (suc ℓ) (t ℓ A) ≈ T ℓ A type

  ≈type-βTπ : Γ ⊢ A ∶ U ℓ →
              (x , T ℓ A) ∷ Γ ⊢ B ∶ U ℓ →
              Γ ⊢ T ℓ (π ℓ x A B) ≈ Π x (T ℓ A) (T ℓ B) type

  ≈type-sym : Γ ⊢ 𝔸  ≈ 𝔸′ type →
              Γ ⊢ 𝔸′ ≈ 𝔸  type

  ≈type-trans : Γ ⊢ 𝔸  ≈ 𝔸′ type →
                Γ ⊢ 𝔸′ ≈ 𝔸″ type →
                Γ ⊢ 𝔸  ≈ 𝔸″ type

_[_/_] : Term → Term → Id → Term
_[_/_] = {!!}

_⟦_/_⟧ : Type → Term → Id → Type
_⟦_/_⟧ = {!!}

-- `x # M` means x is fresh in M
_#_ : Id → Term → Set
_#_ = {!!}

data _⊢_≈_∶_ Γ where
  ≈-u : ⊢ Γ →
        Γ ⊢ u ℓ ≈ u ℓ ∶ U (suc ℓ)

  ≈-t : Γ ⊢ A ≈ A′ ∶ U ℓ →
        Γ ⊢ t ℓ A ≈ t ℓ A′ ∶ U (suc ℓ)

  ≈-π : Γ ⊢ A ≈ A′ ∶ U ℓ →
        (x , T ℓ A) ∷ Γ ⊢ B ≈ B′ ∶ U ℓ →
        Γ ⊢ π ℓ x A B ≈ π ℓ x A′ B′ ∶ U ℓ

  ≈-ƛ : (x , 𝔸) ∷ Γ ⊢ M ≈ M′ ∶ 𝔹 →
        Γ ⊢ ƛ x 𝔸 M ≈ ƛ x 𝔸 M′ ∶ Π x 𝔸 𝔹

  ≈-∙ : Γ ⊢ M ≈ M′ ∶ Π x 𝔸 𝔹 →
        Γ ⊢ N ≈ N′ ∶ 𝔸 →
        Γ ⊢ M ∙ N ≈ M′ ∙ N′ ∶ 𝔹 ⟦ N / x ⟧

  ≈-v : ⊢ Γ →
        x ∶ 𝔸 ∈ Γ →
        Γ ⊢ v x ≈ v x ∶ 𝔸

  ≈-β : (x , 𝔸) ∷ Γ ⊢ M ∶ 𝔹 →
        Γ ⊢ N ∶ 𝔸 →
        Γ ⊢ ƛ x 𝔸 M ∙ N ≈ M [ N / x ] ∶ 𝔹 ⟦ N / x ⟧

  ≈-η : Γ ⊢ M ∶ Π x 𝔸 𝔹 →
        y # M →
        Γ ⊢ M ≈ ƛ y 𝔸 (M ∙ v y) ∶ Π x 𝔸 𝔹

  ≈-sym : Γ ⊢ M  ≈ M′ ∶ 𝔸 →
          Γ ⊢ M′ ≈ M  ∶ 𝔸

  ≈-trans : Γ ⊢ M  ≈ M′ ∶ 𝔸 →
            Γ ⊢ M′ ≈ M″ ∶ 𝔸 →
            Γ ⊢ M  ≈ M″ ∶ 𝔸

  ≈-≈type : Γ ⊢ 𝔸 ≈ 𝔸′ type →
            Γ ⊢ M ≈ M′ ∶ 𝔸 →
            Γ ⊢ M ≈ M′ ∶ 𝔸′

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
true⇒ctx (≈-ƛ J) = case true⇒ctx J of λ { (⊢∷ ⊢Γ _) → ⊢Γ }
true⇒ctx (≈-∙ J _) = true⇒ctx J
true⇒ctx (≈-v ⊢Γ _) = ⊢Γ
true⇒ctx (≈-β _ J) = true⇒ctx J
true⇒ctx (≈-η J _) = true⇒ctx J
true⇒ctx (≈-sym J) = true⇒ctx J
true⇒ctx (≈-trans J _) = true⇒ctx J
true⇒ctx (≈-≈type J _) = type⇒ctx J

⊢U : [] ⊢ U ℓ type
⊢U = ≈type-U ⊢[]

⊢Tu : [] ⊢ T (suc ℓ) (u ℓ) type
⊢Tu = ≈type-T (≈-u ⊢[])

⊢id : Γ ⊢ 𝔸 type → Γ ⊢ ƛ x 𝔸 (v x) ∶ Π x 𝔸 𝔸
⊢id J = ≈-ƛ (≈-v (⊢∷ (type⇒ctx J) J) First.[ refl , refl ])

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

⊢Πx,x : [] ⊢ T (suc ℓ) (π (suc ℓ) x (u ℓ) (t ℓ (v x))) ≈ Π x (U ℓ) (T ℓ (v x)) type
⊢Πx,x {ℓ = ℓ} {x = x} = begin[ [] ]
  T (suc ℓ) (π (suc ℓ) x (u ℓ) (t ℓ (v x)))     ≈type⟨ ≈type-βTπ (≈-u ⊢[]) (≈-t J₂) ⟩
  Π x (T (suc ℓ) (u ℓ)) (T (suc ℓ) (t ℓ (v x))) ≈type[ ≈type-Π (≈type-βTu ⊢[]) (≈type-βTt J₂) ]
  Π x (U ℓ) (T ℓ (v x))
  where
    open ≈type-Reasoning

    J₁ : ⊢ (x , T (suc ℓ) (u ℓ)) ∷ []
    J₁ = ⊢∷ ⊢[] (≈type-T (≈-u ⊢[]))

    J₂ : (x , T (suc ℓ) (u ℓ)) ∷ [] ⊢ v x ∶ U ℓ
    J₂ = ≈-≈type {𝔸 = T (suc ℓ) (u ℓ)}
                 (≈type-βTu J₁)
                 (≈-v J₁ First.[ refl , refl ])
