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

monoid×-₀ : Monoid 0ℓ 0ℓ → Setoid 0ℓ 0ℓ → Setoid 0ℓ 0ℓ
monoid×-₀ record { Carrier = Carrierₘ ; _≈_ = _≈ₘ_ ; isMonoid = isMonoid } record { Carrier = Carrier ; _≈_ = _≈_ ; isEquivalence = isEquivalence } = record
  { Carrier = Carrierₘ × Carrier
  ; _≈_ = λ (x₁ , y₁) (x₂ , y₂) → x₁ ≈ₘ x₂ × y₁ ≈ y₂
  ; isEquivalence = record
      { refl = IsEquivalence.refl isEquivalenceₘ , IsEquivalence.refl isEquivalence
      ; sym = λ (fst , snd) → IsEquivalence.sym isEquivalenceₘ fst , IsEquivalence.sym isEquivalence snd
      ; trans = λ (fst₁ , snd₁) (fst₂ , snd₂) → IsEquivalence.trans isEquivalenceₘ fst₁ fst₂ , IsEquivalence.trans isEquivalence snd₁ snd₂
      }
  } where isEquivalenceₘ = IsMagma.isEquivalence $ IsSemigroup.isMagma $ IsMonoid.isSemigroup isMonoid

monoid×-₁ : ∀ {A B : Setoid 0ℓ 0ℓ} → (m : Monoid 0ℓ 0ℓ) → (f : Setoids 0ℓ 0ℓ [ A , B ]) → Setoids 0ℓ 0ℓ [ monoid×-₀ m A , monoid×-₀ m B ]
monoid×-₁ _ record { _⟨$⟩_ = f ; cong = cong } = record
  { _⟨$⟩_ = λ (fst ,  snd) → fst , f snd
  ; cong = λ (fst , snd) → fst , cong snd
  }

monoid×-hom : {x y z : Setoid 0ℓ 0ℓ} {m : Monoid zero zero} {x₁ y₁ : Σ (Carrier m) (λ _ → Setoid.Carrier x)}
    → (f : Π x (indexedSetoid y))
    → (g : Π y (indexedSetoid z))
    → (x Setoid.≈ proj₂ x₁) (proj₂ y₁)
    → (z Setoid.≈ g ⟨$⟩ (f ⟨$⟩ proj₂ x₁)) (g ⟨$⟩ (f ⟨$⟩ proj₂ y₁))
monoid×-hom record { cong = congᵐ } record { cong = cong } p = cong $ congᵐ p

monoid×-endo : Monoid 0ℓ 0ℓ → Endofunctor (Setoids 0ℓ 0ℓ)
monoid×-endo m =  record
  { F₀ = monoid×-₀ m
  ; F₁ = monoid×-₁ m
  ; identity = λ x → x
  ; homomorphism = λ {_} {_} {_} {f} {g} {x₁} {y₁} (fst , snd) → fst , monoid×-hom {_} {_} {_} {m} {x₁} {y₁} f g snd
  ; F-resp-≈ = λ x (fst , snd) → fst , x snd
  }

monoid×-η : (m : Monoid 0ℓ 0ℓ) → NaturalTransformation idF (monoid×-endo m)
monoid×-η record { ε = ε ; isMonoid = isMonoid } = record
  { η = λ _ → record { _⟨$⟩_ = λ x → ε , x ; cong = λ x → isEquivalenceᵐ , x }
  ; commute = λ f x → isEquivalenceᵐ , cong f x
  ; sym-commute = λ f x → isEquivalenceᵐ , cong f x
  } where
  isEquivalenceᵐ = IsEquivalence.refl $ IsMagma.isEquivalence $ IsSemigroup.isMagma $ IsMonoid.isSemigroup isMonoid

monoid×μ : (m : Monoid 0ℓ 0ℓ) → NaturalTransformation (monoid×-endo m ∘F monoid×-endo m) (monoid×-endo m)
monoid×μ record { _∙_ = _∙_ ; isMonoid = isMonoid } = record
  { η = λ X → record { _⟨$⟩_ =  λ { (d , d₁ , value) → ( d ∙ d₁) , value } ; cong = λ { (d , d₁ , v) → congₘ d d₁ , v } }
  ; commute = λ { record { cong = cong } (d , d₁ , v) → congₘ d d₁ , cong v }
  ; sym-commute = λ { record { cong = cong } (d , d₁ , v) → congₘ d d₁ , cong v }
  } where
  congₘ = IsMagma.∙-cong $ IsSemigroup.isMagma $ IsMonoid.isSemigroup isMonoid

monoid×-monad : Monoid 0ℓ 0ℓ → Monad (Setoids 0ℓ 0ℓ)
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
