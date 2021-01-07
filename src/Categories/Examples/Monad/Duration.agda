{-# OPTIONS --safe --without-K #-}
module Duration where

open import Level

open import Function.Equality using (Π; _⟨$⟩_; cong)

open import Relation.Binary
open import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial

open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Algebra using (Monoid)

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Functor renaming (id to idF)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Monad using (Monad)

open import Data.Nat.Properties renaming (+-0-monoid to +-0-nat-monoid)
open import Data.Integer.Properties renaming (+-0-monoid to +-0-integer-monoid)
open import Data.Rational.Properties renaming (+-0-monoid to +-0-rational-monoid)

open Monoid public

monoid×-₀ : ∀ {l} → Monoid l l → Setoid l l → Setoid l l
monoid×-₀ m s = record
  { Carrier = Carrierₘ × Carrierₛ
  ; _≈_ = λ (x₁ , y₁) (x₂ , y₂) → x₁ ≈ₘ x₂ × y₁ ≈ₛ y₂
  ; isEquivalence = record
      { refl = refl isEquivalenceₘ , refl isEquivalenceₛ
      ; sym = λ (x₁≈x₂ , y₁≈y₂) → sym isEquivalenceₘ x₁≈x₂ , sym isEquivalenceₛ y₁≈y₂
      ; trans = λ (x₁≈x₂ , y₁≈y₂) (x₂≈x₃ , y₂≈y₃) → trans isEquivalenceₘ x₁≈x₂ x₂≈x₃ , trans isEquivalenceₛ y₁≈y₂ y₂≈y₃
      }
  }
  where
    module m = Monoid m
    module s = Setoid s
    open m renaming (Carrier to Carrierₘ; _≈_ to _≈ₘ_; isEquivalence to isEquivalenceₘ)
    open s renaming (Carrier to Carrierₛ; _≈_ to _≈ₛ_; isEquivalence to isEquivalenceₛ)
    open IsEquivalence

monoid×-₁ : ∀ {l} {A B : Setoid l l} → (m : Monoid l l) → (f : Setoids l l [ A , B ]) → Setoids l l [ monoid×-₀ m A , monoid×-₀ m B ]
monoid×-₁ _ record { _⟨$⟩_ = f ; cong = cong } = record
  { _⟨$⟩_ = λ (aₘ ,  bₛ) → aₘ , f bₛ
  ; cong = λ (proj₁≈ ,  proj₂≈) → proj₁≈ , cong proj₂≈
  }

monoid×-endo : ∀ {l} → Monoid l l → Endofunctor (Setoids l l)
monoid×-endo m =  record
  { F₀ = monoid×-₀ m
  ; F₁ = monoid×-₁ m
  ; identity = λ x≈y → x≈y
  ; homomorphism = λ { {f = record { cong = congₘ }} {g = record { cong = congₛ }} (proj₁x≈proj₁y , proj₂x≈proj₂y) → proj₁x≈proj₁y , congₛ (congₘ proj₂x≈proj₂y) }
  ; F-resp-≈ = λ f (proj₁≈ , proj₂≈) → proj₁≈ , f proj₂≈
  }

monoid×-η : ∀ {l} → (m : Monoid l l) → NaturalTransformation idF (monoid×-endo m)
monoid×-η m = record
  { η = λ _ → record { _⟨$⟩_ = λ x → εₘ , x ; cong = λ x → refl isEquivalenceₘ , x }
  ; commute = λ f x → refl isEquivalenceₘ , cong f x
  ; sym-commute = λ f x → refl isEquivalenceₘ , cong f x
  }
  where
    module m = Monoid m
    open m renaming (ε to εₘ; isEquivalence to isEquivalenceₘ)
    open IsEquivalence

monoid×-μ : ∀ {l} → (m : Monoid l l) → NaturalTransformation (monoid×-endo m ∘F monoid×-endo m) (monoid×-endo m)
monoid×-μ m = record
  { η = λ X → record
    { _⟨$⟩_ =  λ { (d , d₁ , value) → ( d ∙ₘ d₁) , value }
    ; cong = λ { (d , d₁ , v) → ∙-congₘ d d₁ , v }
    }
  ; commute = λ { record { cong = cong } (d , d₁ , v) → ∙-congₘ d d₁ , cong v }
  ; sym-commute = λ { record { cong = cong } (d , d₁ , v) → ∙-congₘ d d₁ , cong v }
  }
  where
    module m = Monoid m
    open m renaming (_∙_ to _∙ₘ_; ∙-cong to ∙-congₘ)

monoid×-monad : ∀ {l} → Monoid l l → Monad (Setoids l l)
monoid×-monad m = record
  { F = monoid×-endo m
  ; η = monoid×-η m
  ; μ = monoid×-μ m
  ; assoc     = λ { {x = a , b , c , _} {y = a₁ , b₁ , c₁ , _}  (p , p₁ , p₂ , p₃) → transₘ (∙-congₘ p (∙-congₘ p₁ p₂)) (symₘ (assoc m a₁ b₁ c₁)) , p₃ }
  ; sym-assoc = λ { {x = a , b , c , _} {y = a₁ , b₁ , c₁ , _}  (p , p₁ , p₂ , p₃) → transₘ (∙-congₘ (∙-congₘ p p₁) p₂)       (assoc m a₁ b₁ c₁)  , p₃ }
  ; identityˡ  = λ { {x = x} (p₁ , p₂) → trans m (idʳ (proj₁ x)) p₁ , p₂ }
  ; identityʳ  = λ { {x = x} (p₁ , p₂) → trans m (idˡ (proj₁ x)) p₁ , p₂ }
  }
  where
    module m = Monoid m
    open m renaming (∙-cong to ∙-congₘ; identityʳ to idʳ; identityˡ to idˡ; trans to transₘ; sym to symₘ)

natDuration : Monad (Setoids 0ℓ 0ℓ)
natDuration = monoid×-monad +-0-nat-monoid

integerDuration : Monad (Setoids 0ℓ 0ℓ)
integerDuration = monoid×-monad +-0-integer-monoid

rationalDuration : Monad (Setoids 0ℓ 0ℓ)
rationalDuration = monoid×-monad +-0-rational-monoid
