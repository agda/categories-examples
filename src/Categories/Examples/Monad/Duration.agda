{-# OPTIONS --safe --without-K #-}
module Categories.Examples.Monad.Duration where

-- Monad induced by pairing a Monoid and a Setoid
open import Level

open import Function.Base using (_-⟪_⟫-_; _on_; _∘_) renaming (id to id→)
open import Function.Equality using (Π; _⟨$⟩_; cong)

open import Relation.Binary
open import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial

open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂; dmap′; zip; map₁; map₂)
open import Algebra using (Monoid)

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Functor renaming (id to idF)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.Monad using (Monad)

open import Data.Nat.Properties renaming (+-0-monoid to +-0-nat-monoid)
open import Data.Integer.Properties renaming (+-0-monoid to +-0-integer-monoid)
open import Data.Rational.Properties renaming (+-0-monoid to +-0-rational-monoid)

open Monoid public

monoid×-₀ : ∀ {l₁ l₂ e₁ e₂} → Monoid l₁ e₁ → Setoid l₂ e₂ → Setoid _ _
monoid×-₀ m s = record
  { Carrier = m.Carrier × s.Carrier
  ; _≈_ = m._≈_ on proj₁ -⟪ _×_ ⟫- s._≈_ on proj₂
  ; isEquivalence = record
      { refl = m.refl , s.refl
      ; sym = dmap′ m.sym s.sym
      ; trans = zip m.trans s.trans
      }
  }
  where
    module m = Monoid m
    module s = Setoid s

monoid×-₁ : ∀ {l₁ l₂ e₁ e₂} {A B : Setoid l₂ e₂} → (m : Monoid l₁ e₁) → (f : Setoids l₂ e₂ [ A , B ]) → Setoids _ _ [ monoid×-₀ m A , monoid×-₀ m B ]
monoid×-₁ _ f = record
  { _⟨$⟩_ = map₂ (_⟨$⟩_ f)
  ; cong = map₂ (cong f)
  }

-- levels have to be the same because everything gets put into the same stop
monoid×-endo : ∀ {l₁ e₁} → Monoid l₁ e₁ → Endofunctor (Setoids l₁ e₁)
monoid×-endo m =  record
  { F₀ = monoid×-₀ m
  ; F₁ = monoid×-₁ m
  ; identity = id→
  ; homomorphism = λ {_} {_} {_} {f} {g} p → map₂ (cong g ∘ cong f) p
  ; F-resp-≈ = λ f → map₂ f
  }

monoid×-η : ∀ {l e} → (m : Monoid l e) → NaturalTransformation idF (monoid×-endo m)
monoid×-η m = ntHelper record
  { η = λ _ → record { _⟨$⟩_ = m.ε ,_ ; cong = m.refl ,_ }
  ; commute = λ f x → m.refl , cong f x
  }
  where module m = Monoid m

monoid×-μ : ∀ {l} → (m : Monoid l l) → NaturalTransformation (monoid×-endo m ∘F monoid×-endo m) (monoid×-endo m)
monoid×-μ m = ntHelper record
  { η = λ X → record
    { _⟨$⟩_ =  λ { (d , d₁ , value) → ( d m.∙ d₁) , value }
    ; cong = λ { (d , d₁ , v) → m.∙-cong d d₁ , v }
    }
  ; commute = λ { f (d , d₁ , v) → m.∙-cong d d₁ , cong f v }
  }
  where
    module m = Monoid m

monoid×-monad : ∀ {l} → Monoid l l → Monad (Setoids l l)
monoid×-monad m = record
  { F = monoid×-endo m
  ; η = monoid×-η m
  ; μ = monoid×-μ m
  ; assoc     = λ (p₀ , p₁ , p₂ , p₃) → m.trans (m.∙-cong p₀ (m.∙-cong p₁ p₂)) (m.sym (m.assoc _ _ _)) , p₃
  ; sym-assoc = λ (p₀ , p₁ , p₂ , p₃) → m.trans (m.∙-cong (m.∙-cong p₀ p₁) p₂) (      (m.assoc _ _ _)) , p₃
  ; identityˡ  = λ p → map₁ (m.trans (m.identityʳ _)) p
  ; identityʳ  = λ p → map₁ (m.trans (m.identityˡ _)) p
  }
  where module m = Monoid m

natDuration : Monad (Setoids 0ℓ 0ℓ)
natDuration = monoid×-monad +-0-nat-monoid

integerDuration : Monad (Setoids 0ℓ 0ℓ)
integerDuration = monoid×-monad +-0-integer-monoid

rationalDuration : Monad (Setoids 0ℓ 0ℓ)
rationalDuration = monoid×-monad +-0-rational-monoid
