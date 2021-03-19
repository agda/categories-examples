{-# OPTIONS --safe --without-K #-}
module Categories.Examples.Functor.Sets where

import Data.List as List
import Data.List.Properties
import Data.Maybe as Maybe
import Data.Maybe.Properties
open import Data.Nat using (ℕ)
import Data.Product as Product
import Data.Vec as Vec
import Data.Vec.Properties
open import Function using (id; λ-; _$-)
open import Relation.Binary.PropositionalEquality using (refl)

open import Categories.Category.Discrete using (Discrete)
open import Categories.Category.Instance.Sets
open import Categories.Functor using (Endofunctor)
open import Categories.Functor.Bifunctor using (Bifunctor; appʳ)

List : ∀ {o} → Endofunctor (Sets o)
List = record
  { F₀ = List.List
  ; F₁ = List.map
  ; identity = map-id $-
  ; homomorphism = map-compose $-
  ; F-resp-≈ = λ f≈g → map-cong (λ- f≈g) $-
  }
  where
    open Data.List.Properties

Maybe : ∀ {o} → Endofunctor (Sets o)
Maybe = record
  { F₀ = Maybe.Maybe
  ; F₁ = Maybe.map
  ; identity = map-id $-
  ; homomorphism = λ {_} {_} {_} {_} {_} {x} → map-compose x
  ; F-resp-≈ = λ f≈g {x} → map-cong (λ- f≈g) x
  }
  where
    open Data.Maybe.Properties

Vec′ : ∀ {o} → Bifunctor (Sets o) (Discrete ℕ) (Sets o)
Vec′ = record
  { F₀ = Product.uncurry Vec.Vec
  ; F₁ = λ { (f , refl) → Vec.map f }
  ; identity = map-id $-
  ; homomorphism = λ { {_} {_} {_} {f , refl} {g , refl} → map-∘ g f _}
  ; F-resp-≈ = λ { {_} {_} {_} {_ , refl} (g , refl) → map-cong (λ- g) _}
  }
  where
    open Product using (_,_)
    open Data.Vec.Properties

Vec : ∀ {o} → ℕ → Endofunctor (Sets o)
Vec = appʳ Vec′
