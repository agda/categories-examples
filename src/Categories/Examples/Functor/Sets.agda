{-# OPTIONS --safe --without-K #-}
module Categories.Examples.Functor.Sets where

import Data.List as List
import Data.List.Properties
open import Function using (id; λ-; _$-)

open import Categories.Category.Instance.Sets
open import Categories.Functor using (Endofunctor)

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
