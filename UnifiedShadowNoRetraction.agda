{-# OPTIONS --cubical --safe --guardedness #-}

module UM_Infinity.UnifiedShadowNoRetraction where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma.Base renaming (Σ to Sigma; _×_ to Times)
open import Cubical.Data.Empty as ⊥ using (⊥; isProp⊥)
open import Cubical.HITs.PropositionalTruncation as PT

------------------------------------------------------------------------
-- Shadow の定義（レベル多相版）
------------------------------------------------------------------------

Shadow :
  {ℓ : Level} →
  (Dynamics Flow : Type ℓ) →
  (collapse : Dynamics → Flow) →
  Typeω
Shadow {ℓ} Dynamics Flow collapse =
  let
    Kernel = Sigma Dynamics (λ d₁ → 
               Sigma Dynamics (λ d₂ → 
                 Times (d₁ ≡ d₂ → ⊥) (collapse d₁ ≡ collapse d₂)))
  in
  -- 任意のレベルの命題 P を導き出せる性質
  ∀ {ℓ'} (P : Type ℓ') → isProp P → (Kernel → P) → P

------------------------------------------------------------------------
-- Unified Shadow No-Retraction Theorem
------------------------------------------------------------------------

Unified-Shadow-No-Retraction :
  {ℓ : Level}
  {Dynamics Flow : Type ℓ}
  (collapse : Dynamics → Flow)
  → Shadow Dynamics Flow collapse
  → (Sigma (Flow → Dynamics) (λ r → (λ x → r (collapse x)) ≡ (λ x → x)))
  → ⊥
Unified-Shadow-No-Retraction {ℓ} {Dynamics} {Flow} collapse shadow (r , ret) =
  shadow ⊥ isProp⊥ (λ kernel-data → 
    let
      -- 1. カーネルのデータを分解
      d₁      = fst kernel-data
      d₂      = fst (snd kernel-data)
      neq     = fst (snd (snd kernel-data))
      coll-eq = snd (snd (snd kernel-data))

      -- 2. 【攻略の鍵】happly をその場で定義します
      -- これによりライブラリのバージョンに関わらず「Not in scope」を回避し、
      -- さらにメタ変数も確実に解消します。
      my-happly : {f g : Dynamics → Dynamics} → f ≡ g → (x : Dynamics) → f x ≡ g x
      my-happly p x = cong (λ h → h x) p

      -- 3. 各点での等式を取り出す
      eq₁ : r (collapse d₁) ≡ d₁
      eq₁ = my-happly ret d₁

      eq₂ : r (collapse d₂) ≡ d₂
      eq₂ = my-happly ret d₂

      -- 4. collapse が等しいなら r を適用しても等しい
      same : r (collapse d₁) ≡ r (collapse d₂)
      same = cong r coll-eq

      -- 5. 鎖状の等式変形で d₁ ≡ d₂ を導出
      d₁≡d₂ : d₁ ≡ d₂
      d₁≡d₂ = sym eq₁ ∙ same ∙ eq₂
    in
      neq d₁≡d₂
  )