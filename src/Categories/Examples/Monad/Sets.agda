{-# OPTIONS --safe --without-K #-}
module Categories.Examples.Monad.Sets where

open import Category.Monad using (RawMonad)
import Data.List as List
import Data.List.Properties
open import Relation.Binary.PropositionalEquality using (refl; sym)

open import Categories.Category.Instance.Sets
open import Categories.Monad using (Monad)
open import Categories.NaturalTransformation using (ntHelper)

import Categories.Examples.Functor.Sets as F

Raw : ∀ {o} (M : Monad (Sets o)) → RawMonad (Monad.F.F₀ M)
Raw M = record
  { return = Monad.η.η M _
  ; _>>=_ = λ Ma f → Monad.μ.η M _ (Monad.F.F₁ M f Ma)
  }

List : ∀ {o} → Monad (Sets o)
List = record
  { F = F.List
  ; η = record
    { η = λ _ → List.[_]
    ; commute = λ _ → refl
    ; sym-commute = λ _ → refl
    }
  ; μ = ntHelper record
    { η = λ _ → List.concat
    ; commute = λ _ {x} → concat-map x
    }
  ; assoc = λ {_} {x} → concat-concat x
  ; sym-assoc = λ {_} {x} → sym (concat-concat x)
  ; identityˡ = concat-[-] _
  ; identityʳ = ++-identityʳ _
  }
  where
    open Data.List.Properties
