{-# OPTIONS --cubical --safe --guardedness #-}

module UM_Infinity.ConcreteShadowProof where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as ⊥ using (⊥; isProp⊥)
open import Cubical.Data.Unit using (Unit; tt) -- Unit型を追加
open import UM_Infinity.Core_Shadow

-- ================================================================
-- 1. 舞台設定
-- ================================================================
data Universe : Type₀ where
  ∅    : Universe
  grow : Universe → Universe

data BinaryWorld : Type₀ where
  Empty : BinaryWorld
  Busy  : BinaryWorld

collapse-to-binary : Universe → BinaryWorld
collapse-to-binary ∅        = Empty
collapse-to-binary (grow _) = Busy

-- ================================================================
-- 4. 具体的な Shadow の証明
-- ================================================================

Universe-Shadow-Exists : Shadow Universe BinaryWorld collapse-to-binary
Universe-Shadow-Exists P P-isProp k-to-p = k-to-p (d₁ , d₂ , neq , coll-eq)
  where
    d₁ = grow ∅
    d₂ = grow (grow ∅)

    coll-eq : collapse-to-binary d₁ ≡ collapse-to-binary d₂
    coll-eq = refl 

    -- growを一段階剥がす関数
    helper : Universe → Universe
    helper ∅        = ∅
    helper (grow u) = u

    -- 【手懐けポイント】判別関数: ∅ならUnit(真)、growなら⊥(偽)を返す
    is∅ : Universe → Type₀
    is∅ ∅        = Unit
    is∅ (grow _) = ⊥

    neq : d₁ ≡ d₂ → ⊥
    neq eq = 
      let 
        -- d₁ ≡ d₂ ならば ∅ ≡ grow ∅
        peq : ∅ ≡ grow ∅
        peq = cong helper eq

        -- ∅ ≡ grow ∅ ならば Unit ≡ ⊥ (真 ≡ 偽)
        unit≡empty : Unit ≡ ⊥
        unit≡empty = cong is∅ peq
      in
      -- Unit ≡ ⊥ という「道」を使って、Unitの要素 tt を ⊥ へ輸送する
      -- これにより ⊥ の要素が捏造され、矛盾が証明される
      transport unit≡empty tt

-- ================================================================
-- 5. 結果
-- ================================================================
Universe-Non-Retraction : ¬ (Sigma (BinaryWorld → Universe) (λ r → (λ x → r (collapse-to-binary x)) ≡ (λ x → x)))
Universe-Non-Retraction = Unified-Shadow-No-Retraction collapse-to-binary Universe-Shadow-Exists