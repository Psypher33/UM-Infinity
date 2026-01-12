{-# OPTIONS --cubical --safe --guardedness #-}

module UM_Infinity.IUT_UM_Bridge01_WorldUniverse where

open import Agda.Primitive using (Level; lzero; lsuc)
open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ; zero; suc)

-- ================================================================
-- IUT side: World = frozen / compressed time
-- ================================================================

record World : Type₀ where
  constructor mkWorld
  field
    tag : ℕ

open World

-- ================================================================
-- UM / CSG side: Universe = sequential growth (natural labeling)
-- ================================================================

data Universe : Type₀ where
  ∅    : Universe
  grow : Universe → Universe

-- ================================================================
-- Collapse: forget growth history, keep only volume
-- ================================================================

collapse : Universe → World
collapse ∅        = mkWorld zero
collapse (grow U) =
  mkWorld (suc (tag (collapse U)))

-- ================================================================
-- Expand: canonical re-growth from frozen time
-- ================================================================

expand : World → Universe
expand (mkWorld zero)    = ∅
expand (mkWorld (suc n)) = grow (expand (mkWorld n))

-- ================================================================
-- Proofs: section & retraction
-- ================================================================

-- section: ∀ U → expand (collapse U) ≡ U
expand-collapse : ∀ U → expand (collapse U) ≡ U
expand-collapse ∅        = refl
expand-collapse (grow U) =
  cong grow (expand-collapse U)

-- retraction: ∀ W → collapse (expand W) ≡ W
collapse-expand : ∀ W → collapse (expand W) ≡ W
collapse-expand (mkWorld zero) = refl
collapse-expand (mkWorld (suc n)) =
  cong (λ w → mkWorld (suc (tag w)))
       (collapse-expand (mkWorld n))

-- ================================================================
-- Isomorphism and Equivalence
-- ================================================================

World≃Universe : World ≃ Universe
World≃Universe =
  isoToEquiv
    (iso expand collapse
         expand-collapse    -- section    : f(g(y)) ≡ y
         collapse-expand)   -- retraction : g(f(x)) ≡ x

World≡Universe : World ≡ Universe
World≡Universe = ua World≃Universe