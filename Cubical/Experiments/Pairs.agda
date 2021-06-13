-- Coherent pairs

{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Experiments.Pairs where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.SIP
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties

open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.Join renaming (inl to jinl ; inr to jinr ; push to jpush)
open import Cubical.HITs.Pushout renaming (inl to pinl ; inr to pinr ; push to ppush)
open import Cubical.HITs.Pushout.Flattening

private
  variable
    ℓ ℓ' : Level

-- prelude (move to lib)
-- propositional extensionality
uaProp : {X Y : hProp ℓ} → (⟨ X ⟩ → ⟨ Y ⟩) → (⟨ Y ⟩ → ⟨ X ⟩) → X ≡ Y
uaProp {ℓ} {X , hX} {Y , hY} f g = TypeOfHLevel≡ 1 (ua (propBiimpl→Equiv hX hY f g))

trueProp→isContr : {A : Type ℓ} → isProp A → A → isContr A
fst (trueProp→isContr h a) = a
snd (trueProp→isContr h a) = h a

-- The type of 2-element sets, i.e., the homotopy type of real projective space, RP∞
TwoEltType : Type (ℓ-suc ℓ-zero)
TwoEltType = TypeWithStr ℓ-zero (λ Y → ∥ Y ≃ Bool ∥)

BoolTwoElt : TwoEltType
BoolTwoElt = (Bool , ∣ idEquiv Bool ∣)

-- some join lemmas (move to Join.Properties?)
module _ (X : Type ℓ) (Y : Type ℓ') where

  joinContr : isContr Y → isContr (join X Y)
  fst (joinContr hY) = jinr (fst hY)
  snd (joinContr hY) (jinl x) i = jpush x (fst hY) (~ i)
  snd (joinContr hY) (jinr y) i = jinr (snd hY y i)
  snd (joinContr hY) (jpush x y j) i =
    hcomp (λ k → λ { (i = i0) → jinr (snd hY y (~ k))
                   ; (i = i1) → jpush x y j
                   ; (j = i0) → jpush x (snd hY y (~ k)) (~ i)
                   ; (j = i1) → jinr (snd hY y (i ∨ (~ k))) })
          (jpush x y ((~ i) ∨ j))

module _ (X : Type ℓ) where

  -- homotopy unordered pairs
  hUP : Type (ℓ-max ℓ (ℓ-suc ℓ-zero))
  hUP = Σ[ K ∈ TwoEltType ] (⟨ K ⟩ → X)

  private
    f : TwoEltType × X → X
    f (K , x) = x

    g : TwoEltType × X → hUP
    g (K , x) = K , λ _ → x

  -- the type of unordered pairs
  UP : Type (ℓ-max ℓ (ℓ-suc ℓ-zero))
  UP = Pushout f g

  -- UP is a set if X is:
  -- consider a fixed pair {x₀ , x₁}
  module _ (H : isSet X) (x₀ x₁ : X) where

    hbase : hUP
    hbase = (BoolTwoElt , λ b → if b then x₀ else x₁)

    base : UP
    base = Pushout.inr hbase

    P : Type _
    P = x₀ ≡ x₁

    isPropP : isProp P
    isPropP = H x₀ x₁

    -- all the primed stuff concerns the simple version
    -- of the path space at base
    f' : TwoEltType × P → P
    f' (K , p) = p

    R : Type _
    R = Pushout {A = P} {B = Unit} {C = TwoEltType × P}
                (λ _ → tt) (λ p → BoolTwoElt , p)

    g' : TwoEltType × P → R
    g' (K , p) = pinr (K , p)

    g'' : P → TwoEltType → R
    g'' p K = g' (K , p)

    D' : Type _
    D' = Pushout f' g'

    g''-inv : R → TwoEltType
    g''-inv (pinl tt) = BoolTwoElt
    g''-inv (pinr (K , _)) = K
    g''-inv (ppush _ i) = BoolTwoElt

    g''-sect : (p : P) → section (g'' p) g''-inv
    g''-sect p (pinl tt) = sym (Pushout.push p)
    g''-sect p (pinr (K , p')) = cong pinr λ i → (K , isPropP p p' i)
    g''-sect p (ppush p' i) j =
      hcomp (λ k → λ { (i = i0) → ppush (isPropP p p' (~ k)) (~ j)
                     ; (i = i1) → pinr (BoolTwoElt , isPropP p p' (j ∨ (~ k)))
                     ; (j = i0) → pinr (BoolTwoElt , isPropP p p' (~ k))
                     ; (j = i1) → ppush p' i }) (ppush p' (i ∨ (~ j)))

    lemma' : (r : R) → Path D' (pinr (pinl tt)) (pinr r)
    lemma' (pinl tt) = refl
    lemma' (pinr (K , p)) = cong pinr (ppush p) ∙∙ sym (ppush (BoolTwoElt , p)) ∙∙ ppush (K , p)
    lemma' (ppush p i) j =
      hcomp (λ k → λ { (i = i0) → r (~ k)
                     ; (i = i1) → doubleCompPath-filler r (sym q) q k j
                     ; (j = i0) → r (~ k)
                     ; (j = i1) →
            hcomp (λ h → λ { (i = i0) → r ((~ k) ∨ (~ h))
                           ; (i = i1) → q (k ∨ (~ h))
                           ; (k = i0) → q ((~ i) ∨ (~ h))
                           ; (k = i1) → r (i ∨ (~ h)) }) (r i1)})
            (q ((~ i) ∨ (~ j)))
      where
        q : Path D' (pinl p) (pinr (pinr (BoolTwoElt , p)))
        q = ppush (BoolTwoElt , p)

        r : Path D' (pinr (pinl tt)) (pinr (pinr (BoolTwoElt , p)))
        r = cong pinr (ppush p)

    thm' : isContr D'
    fst thm' = pinr (pinl tt)
    snd thm' (pinl p) = sym (ppush (g''-inv (pinl tt) , p) ∙ cong pinr (g''-sect p (pinl tt)))
    snd thm' (pinr r) = lemma' r
    snd thm' (ppush (K , p) i) j =
      hcomp (λ k → λ { (i = i0) → doubleCompPath-filler r (sym q) refl k j
                     ; (i = i1) → doubleCompPath-filler r (sym q) s k j
                     ; (j = i0) → r (~ k)
                     ; (j = i1) → s (i ∧ k)}) (q (~ j))
      where
        q : Path D' (pinl p) (pinr (pinr (BoolTwoElt , p)))
        q = ppush (BoolTwoElt , p)

        r : Path D' (pinr (pinl tt)) (pinr (pinr (BoolTwoElt , p)))
        r = cong pinr (ppush p)

        s : Path D' (pinl p) (pinr (pinr (K , p)))
        s = ppush (K , p)


    -- now we compare this to what we get from the flattening lemma
    F : X → Type ℓ
    F x = (x ≡ x₀) × (x ≡ x₁)

    G : hUP → Type ℓ
    G (K , w) = join
      (Σ[ e ∈ Bool ≃ ⟨ K ⟩ ] (w (equivFun e true) ≡ x₀) × (w (equivFun e false) ≡ x₁))
      (P × ((k : ⟨ K ⟩) → w k ≡ x₀))

    lemma : (K : TwoEltType) (x : X) (p : F x)
             → isContr (G (K , λ _ → x))
    lemma K x (p₀ , p₁) = joinContr _ _ (trueProp→isContr
      (isProp× isPropP (isPropΠ λ _ → H x x₀)) (sym p₀ ∙ p₁ , λ _ → p₀) )

    Q : (z : TwoEltType × X) → F (f z) ≃ G (g z)
    Q (K , x) = isoToEquiv (iso to from to-from from-to)
      where
        H₀₁ : isProp ((x ≡ x₀) × (x ≡ x₁))
        H₀₁ = isProp× (H x x₀) (H x x₁)

        to : (x ≡ x₀) × (x ≡ x₁) → join
          (Σ[ e ∈ Bool ≃ ⟨ K ⟩ ] (x ≡ x₀) × (x ≡ x₁))
          ((x₀ ≡ x₁) × (⟨ K ⟩ → x ≡ x₀))
        to p = fst (lemma K x p)

        from : join (Σ[ e ∈ Bool ≃ ⟨ K ⟩ ] (x ≡ x₀) × (x ≡ x₁))
                    ((x₀ ≡ x₁) × (⟨ K ⟩ → x ≡ x₀))
               → (x ≡ x₀) × (x ≡ x₁)
        from (jinl (e , p)) = p
        from (jinr (p₀₁ , q)) = rec H₀₁
          (λ e → q (invEquiv e .fst true) , q (invEquiv e .fst true) ∙ p₀₁ ) (snd K)
        from (jpush z p i) = isProp→PathP (λ _ → H₀₁) (from (jinl z)) (from (jinr p)) i

        to-from : (z : join (Σ[ e ∈ Bool ≃ ⟨ K ⟩ ] (x ≡ x₀) × (x ≡ x₁))
                    ((x₀ ≡ x₁) × (⟨ K ⟩ → x ≡ x₀))) → to (from z) ≡ z
        to-from z = sym (Hjoin .snd (to (from z))) ∙ Hjoin .snd z
          where
            Hjoin : isContr (join (Σ[ e ∈ Bool ≃ ⟨ K ⟩ ] (x ≡ x₀) × (x ≡ x₁))
                                  ((x₀ ≡ x₁) × (⟨ K ⟩ → x ≡ x₀)))
            Hjoin = lemma K x (from z)

        from-to : (z : (x ≡ x₀) × (x ≡ x₁)) → from (to z) ≡ z
        from-to z = H₀₁ (from (to z)) z

    open FlatteningLemma f g F G Q

    D : Type _
    D = Pushout Σf Σg

{-
  Need functoriality of pushouts to do this
    thm : isContr D
    thm = ?
-}
