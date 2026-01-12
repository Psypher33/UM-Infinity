{-# OPTIONS --cubical --safe --guardedness #-}

module UM_Infinity.Bridge01_WorldUniverse_Shadow where

open import Cubical.Foundations.Prelude
open import UM_Infinity.Core_Shadow

module _ {ℓ : Level} {D F : Type ℓ} (c : D → F) where

  -- Core_Shadow が public インポートしているため、ここで Sigma が使えます
  World-Universe-Incomputable :
    Shadow D F c → ¬ (Sigma (F → D) (λ r → (λ x → r (c x)) ≡ (λ x → x)))
  World-Universe-Incomputable s ret = Unified-Shadow-No-Retraction c s ret