{-# OPTIONS --safe --without-K #-}
module Duration where

open import Level

open import Function using (_$_)
open import Function.Equality using (Π; _⟨$⟩_; cong)

open import Relation.Binary
open import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial

open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Algebra using (Monoid; IsMonoid; IsSemigroup; IsMagma)

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
  { _⟨$⟩_ = λ (fst ,  snd) → fst , f snd
  ; cong = λ (fst , snd) → fst , cong snd
  }

monoid×-hom : let open Setoid renaming (Carrier to Carrierₛ) in
    ∀ {l} {x y z : Setoid l l} {m : Monoid l l} {x₁ y₁ : Σ (Carrier m) (λ _ → Carrierₛ x)}
    → (f : Π x (indexedSetoid y))
    → (g : Π y (indexedSetoid z))
    → let open Setoid x renaming (_≈_ to _≈ₓ_) in (proj₂ x₁) ≈ₓ (proj₂ y₁)
    → let open Setoid z renaming (_≈_ to _≈ₛ_) in (g ⟨$⟩ (f ⟨$⟩ proj₂ x₁)) ≈ₛ (g ⟨$⟩ (f ⟨$⟩ proj₂ y₁))
monoid×-hom record { cong = congₘ } record { cong = congₛ } p = congₛ $ congₘ p

monoid×-endo : ∀ {l} → Monoid l l → Endofunctor (Setoids l l)
monoid×-endo m =  record
  { F₀ = monoid×-₀ m
  ; F₁ = monoid×-₁ m
  ; identity = λ x → x
  ; homomorphism = λ {_} {_} {_} {f} {g} {x₁} {y₁} (fst , snd) → fst , monoid×-hom {_} {_} {_} {_} {m} {x₁} {y₁} f g snd
  ; F-resp-≈ = λ x (fst , snd) → fst , x snd
  }

monoid×-η : ∀ {l} → (m : Monoid l l) → NaturalTransformation idF (monoid×-endo m)
monoid×-η record { ε = ε ; isMonoid = isMonoid } = record
  { η = λ _ → record { _⟨$⟩_ = λ x → ε , x ; cong = λ x → isEquivalenceᵐ , x }
  ; commute = λ f x → isEquivalenceᵐ , cong f x
  ; sym-commute = λ f x → isEquivalenceᵐ , cong f x
  } where
  isEquivalenceᵐ = IsEquivalence.refl $ IsMagma.isEquivalence $ IsSemigroup.isMagma $ IsMonoid.isSemigroup isMonoid

monoid×μ : ∀ {l} → (m : Monoid l l) → NaturalTransformation (monoid×-endo m ∘F monoid×-endo m) (monoid×-endo m)
monoid×μ record { _∙_ = _∙_ ; isMonoid = isMonoid } = record
  { η = λ X → record { _⟨$⟩_ =  λ { (d , d₁ , value) → ( d ∙ d₁) , value } ; cong = λ { (d , d₁ , v) → congₘ d d₁ , v } }
  ; commute = λ { record { cong = cong } (d , d₁ , v) → congₘ d d₁ , cong v }
  ; sym-commute = λ { record { cong = cong } (d , d₁ , v) → congₘ d d₁ , cong v }
  } where
  congₘ = IsMagma.∙-cong $ IsSemigroup.isMagma $ IsMonoid.isSemigroup isMonoid

monoid×-monad : ∀ {l} → Monoid l l → Monad (Setoids l l)
monoid×-monad m = record
    { F = monoid×-endo m
    ; η = monoid×-η m
    ; μ = monoid×μ m
    ; assoc     = λ { {x = a , b , c , _} {y = a₁ , b₁ , c₁ , _}  (p , p₁ , p₂ , p₃) → transᵐ (congᵐ p (congᵐ p₁ p₂)) (symᵐ (assoc m a₁ b₁ c₁)) , p₃ }
    ; sym-assoc = λ { {x = a , b , c , _} {y = a₁ , b₁ , c₁ , _}  (p , p₁ , p₂ , p₃) → transᵐ (congᵐ (congᵐ p p₁) p₂)       (assoc m a₁ b₁ c₁)  , p₃ }
    ; identityˡ  = λ { {x = x} (p₁ , p₂) → trans m (idʳ (proj₁ x)) p₁ , p₂ }
    ; identityʳ  = λ { {x = x} (p₁ , p₂) → trans m (idˡ (proj₁ x)) p₁ , p₂ }
    } where
    congᵐ = IsMagma.∙-cong $ IsSemigroup.isMagma $ IsMonoid.isSemigroup $ Monoid.isMonoid m
    symᵐ = IsMonoid.sym $ Monoid.isMonoid m
    transᵐ = IsMonoid.trans $ Monoid.isMonoid m
    idʳ = IsMonoid.identityʳ $ Monoid.isMonoid m
    idˡ = IsMonoid.identityˡ $ Monoid.isMonoid m

natDuration : Monad (Setoids 0ℓ 0ℓ)
natDuration = monoid×-monad +-0-nat-monoid

integerDuration : Monad (Setoids 0ℓ 0ℓ)
integerDuration = monoid×-monad +-0-integer-monoid

rationalDuration : Monad (Setoids 0ℓ 0ℓ)
rationalDuration = monoid×-monad +-0-rational-monoid
