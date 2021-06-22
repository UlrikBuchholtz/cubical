{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Experiments.JoinLoopAdjunction where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Pointed.Adjunction

open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.HomotopyGroup

open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.Susp
open import Cubical.HITs.Susp.LoopAdjunction
open import Cubical.HITs.Join
open import Cubical.HITs.SmashProduct

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace

private
  variable
    ℓ ℓA ℓA' ℓA'' ℓB ℓX ℓX' ℓX'' : Level

σ : (A : Pointed ℓA) → (typ A) → typ (Ω (∙Susp (typ A)))
σ A a = merid a ∙ sym (merid (pt A))

∙join : ∀ {ℓA ℓB} → Pointed ℓA → Pointed ℓB → Pointed (ℓ-max ℓA ℓB)
fst (∙join A B) = join (typ A) (typ B)
snd (∙join A B) = inl (pt A)

lCancelOuter : {A : Type ℓ}{x y : A}(p : x ≡ y) → p ⁻¹ ∙∙ refl ∙∙ p ≡ refl
lCancelOuter p i j =
  hcomp (λ k → λ { (i = i0) → doubleCompPath-filler (sym p) refl p k j
    ; (i = i1) → p k
    ; (j = i0) → p k
    ; (j = i1) → p k}) (p i0)

conj : {A : Type ℓ}{x y : A}(q : x ≡ y)(p : x ≡ x) → y ≡ y
conj q p = sym q ∙∙ p ∙∙ q

conj-refl : {A : Type ℓ}{x : A}(p : x ≡ x) → conj refl p ≡ p
conj-refl p = sym (rUnit p)

isHomogeneousΩ : (A : Pointed ℓ) → isHomogeneous (Ω A)
isHomogeneousΩ A = isHomogeneousPath (typ A) refl

module _ (A : Pointed ℓA)(B : Pointed ℓB) where
  τ : typ A → typ B → typ (Ω (∙join A B))
  τ a b = (push (pt A) (pt B) ∙ sym (push a (pt B))) ∙∙ push a b ∙∙ sym (push (pt A) b)

  τ-pt-l : (b : typ B) → τ (pt A) b ≡ refl
  τ-pt-l b =
    (push (pt A) (pt B) ∙ sym (push (pt A) (pt B))) ∙∙ push (pt A) b ∙∙ sym (push (pt A) b)
      ≡⟨ cong (λ q → q ∙∙ push (pt A) b ∙∙ sym (push (pt A) b)) (rCancel (push (pt A) (pt B))) ⟩
    (refl ∙∙ push (pt A) b ∙∙ sym (push (pt A) b))
      ≡⟨ rCancel (push (pt A) b) ⟩
    refl ∎

  τ-pt-r : (a : typ A) → τ a (pt B) ≡ refl
  τ-pt-r a =
    (push (pt A) (pt B) ∙ sym (push a (pt B))) ∙∙ push a (pt B) ∙∙ sym (push (pt A) (pt B))
      ≡⟨ doubleCompPath-elim _ _ _ ⟩
    ((push (pt A) (pt B) ∙ sym (push a (pt B))) ∙ push a (pt B)) ∙ sym (push (pt A) (pt B))
      ≡⟨ cong (λ q → q ∙ sym (push (pt A) (pt B)))
              (sym (assoc (push (pt A) (pt B)) (sym (push a (pt B))) (push a (pt B)))) ⟩
    (push (pt A) (pt B) ∙ (sym (push a (pt B)) ∙ push a (pt B))) ∙ sym (push (pt A) (pt B))
      ≡⟨ cong (λ q → (push (pt A) (pt B) ∙ q) ∙ sym (push (pt A) (pt B)))
              (lCancel (push a (pt B))) ⟩
    (push (pt A) (pt B) ∙ refl) ∙ sym (push (pt A) (pt B))
      ≡⟨ cong (λ q → q ∙ sym (push (pt A) (pt B))) (sym (rUnit (push (pt A) (pt B)))) ⟩
    push (pt A) (pt B) ∙ sym (push (pt A) (pt B))
      ≡⟨ rCancel (push (pt A) (pt B)) ⟩
    refl ∎

-- adjunction between join and mapping to the loop space
module _ (B : Pointed ℓB) where

  join-mapₗ : {A : Pointed ℓA} {A' : Pointed ℓA'}
    → (A →∙ A') → (∙join A B →∙ ∙join A' B)
  fst (join-mapₗ f) (inl a) = inl (fst f a)
  fst (join-mapₗ f) (inr b) = inr b
  fst (join-mapₗ f) (push a b i) = push (fst f a) b i
  snd (join-mapₗ f) i = inl (snd f i)

  join-mapₗ-∘∙ : {A : Pointed ℓA}{A' : Pointed ℓA'}{A'' : Pointed ℓA''}
               → (f' : A' →∙ A'') → (f : A →∙ A')
               → join-mapₗ (f' ∘∙ f) ≡ join-mapₗ f' ∘∙ join-mapₗ f
  fst (join-mapₗ-∘∙ f' f i) (inl a) = inl (fst f' (fst f a))
  fst (join-mapₗ-∘∙ f' f i) (inr b) = inr b
  fst (join-mapₗ-∘∙ f' f i) (push a b j) = push (fst f' (fst f a)) b j
  snd (join-mapₗ-∘∙ f' f i) = cong-∙ inl (cong (fst f') (snd f)) (snd f') i

  lpmap-mapₗ : {X : Pointed ℓX} {X' : Pointed ℓX'}
    → (X →∙ X') → (B →∙ Ω X ∙) →∙ (B →∙ Ω X' ∙)
  fst (fst (lpmap-mapₗ g) f) b = conj (snd g) (cong (fst g) (fst f b))
  snd (fst (lpmap-mapₗ g) f) = cong (conj (snd g)) (cong (cong (fst g)) (snd f))
                               ∙ lCancelOuter (snd g)
  snd (lpmap-mapₗ {X' = X'} g) = →∙Homogeneous≡ (isHomogeneousΩ X')
                                 (funExt (λ b → lCancelOuter (snd g)))

  lpmap-homogeneous : (X : Pointed ℓX) → isHomogeneous (B →∙ Ω X ∙)
  lpmap-homogeneous X = isHomogeneous→∙ (isHomogeneousΩ X)

  lpmap-mapₗ-∘∙ : {X : Pointed ℓX}{X' : Pointed ℓX'}{X'' : Pointed ℓX''}
               → (g' : X' →∙ X'') → (g : X →∙ X')
               → lpmap-mapₗ (g' ∘∙ g) ≡ lpmap-mapₗ g' ∘∙ lpmap-mapₗ g
  lpmap-mapₗ-∘∙ {X = X} {X'' = X''} g' g = →∙Homogeneous≡ (lpmap-homogeneous X'') (funExt lemma₁)
    where
      lemma₁ : (f : B →∙ Ω X)
            → fst (lpmap-mapₗ (g' ∘∙ g)) f ≡ fst (lpmap-mapₗ g' ∘∙ lpmap-mapₗ g) f
      lemma₁ f = →∙Homogeneous≡ (isHomogeneousΩ X'') (funExt lemma₂)
        where
          lemma₂ : (b : typ B)
            → fst (fst (lpmap-mapₗ (g' ∘∙ g)) f) b
            ≡ fst (fst (lpmap-mapₗ g' ∘∙ lpmap-mapₗ g) f) b
          lemma₂ b i j = hcomp
            (λ k → λ { (i = i0) → doubleCompPath-filler (sym p)
                                (λ t → fst g' (fst g (fst f b t))) p k j
                     ; (i = i1) → doubleCompPath-filler (sym (snd g'))
                                (cong (fst g') (conj (snd g) (cong (fst g) (fst f b))))
                                (snd g') k j
                     ; (j = i0) → sq i k
                     ; (j = i1) → sq i k})
            (fst g' (doubleCompPath-filler (sym (snd g)) (cong (fst g) (fst f b)) (snd g) i j))
            where
              p = cong (fst g') (snd g) ∙ snd g'
              sq : Square p (snd g') (cong (fst g') (snd g)) refl
              sq i j = hcomp
                (λ k → λ { (i = i0) → doubleCompPath-filler
                              refl (cong (fst g') (snd g)) (snd g') k j
                         ; (i = i1) → snd g' (j ∧ k)
                         ; (j = i0) → fst g' (snd g i)
                         ; (j = i1) → snd g' k}) (fst g' (snd g (i ∨ j)))

  jlp-unit : (A : Pointed ℓA) → A →∙ (B →∙ Ω (∙join A B) ∙)
  fst (fst (jlp-unit A) a) b = τ A B a b
  snd (fst (jlp-unit A) a) = τ-pt-r A B a
  snd (jlp-unit A) = →∙Homogeneous≡ (isHomogeneousΩ (∙join A B)) (funExt (τ-pt-l A B))

  jlp-unit-nat : {A : Pointed ℓA}{A' : Pointed ℓA'}(f : A →∙ A')
    → lpmap-mapₗ (join-mapₗ f) ∘∙ jlp-unit A ≡ jlp-unit A' ∘∙ f
  jlp-unit-nat {A = A} {A' = A'} f = →∙Homogeneous≡ (lpmap-homogeneous _) (funExt lemma₁)
    where
      lemma₁ : (a : typ A) → fst (lpmap-mapₗ (join-mapₗ f) ∘∙ jlp-unit A) a
                           ≡ fst (jlp-unit A' ∘∙ f) a
      lemma₁ a = →∙Homogeneous≡ (isHomogeneousΩ (∙join A' B)) (funExt lemma₂)
        where
          g = (join-mapₗ f)

          sq : (b : typ B) → Square (snd g) (sym (push (pt A') b)) (push (fst f (pt A)) b) refl
          sq b i j = hcomp
            (λ k → λ { (i = i0) → snd g (j ∨ (~ k))
                     ; (i = i1) → push (pt A') b (~ j)
                     ; (j = i0) → push (snd f (~ k)) b i
                     ; (j = i1) → inl (pt A')}) (push (pt A') b (i ∧ (~ j)))

          lemma₂ : (b : typ B)
            → fst (fst (lpmap-mapₗ (join-mapₗ f) ∘∙ jlp-unit A) a) b
            ≡ fst (fst (jlp-unit A' ∘∙ f) a) b
          lemma₂ b i j = hcomp
            (λ k → λ { (i = i0) → doubleCompPath-filler (sym (snd g)) (cong (fst g)
                                  (τ A B a b)) (snd g) k j
                     ; (i = i1) → doubleCompPath-filler
                                  (push (pt A') (pt B) ∙ sym (push (fst f a) (pt B)))
                                  (push (fst f a) b) (sym (push (pt A') b)) k j
                     ; (j = i0) → hcomp
                     (λ j → λ { (i = i0) → snd g k
                              ; (i = i1) → doubleCompPath-filler (push (fst f a) (pt B))
                                   (sym (push (pt A') (pt B))) refl j k
                              ; (k = i0) → fst g (doubleCompPath-filler refl (push (pt A) (pt B))
                                   (sym (push a (pt B))) j i)
                              ; (k = i1) → inl (pt A')}) (sq (pt B) i k)
                     ; (j = i1) → sq b i k})
            (fst g (doubleCompPath-filler (push (pt A) (pt B) ∙ sym (push a (pt B)))
                                          (push a b) (sym (push (pt A) b)) (~ i) j))

  jlp-counit : (X : Pointed ℓX) → (∙join (B →∙ Ω X ∙) B) →∙ X
  fst (jlp-counit X) (inl f) = pt X
  fst (jlp-counit X) (inr b) = pt X
  fst (jlp-counit X) (push f b i) = fst f b i
  snd (jlp-counit X) = refl

  jlp-counit-nat : {X : Pointed ℓX}{X' : Pointed ℓX'}(g : X →∙ X')
    → jlp-counit X' ∘∙ join-mapₗ (lpmap-mapₗ g) ≡ g ∘∙ jlp-counit X
  fst (jlp-counit-nat g i) (inl f) = snd g (~ i)
  fst (jlp-counit-nat g i) (inr b) = snd g (~ i)
  fst (jlp-counit-nat g i) (push f b j) = doubleCompPath-filler
    (sym (snd g)) (cong (fst g) (fst f b)) (snd g) (~ i) j
  snd (jlp-counit-nat g i) j = hcomp
    (λ k → λ { (i = i0) → doubleCompPath-filler {x = snd g i1} refl refl refl k j
             ; (i = i1) → doubleCompPath-filler refl refl (snd g) k j
             ; (j = i0) → snd g (~ i)
             ; (j = i1) → snd g (~ i ∨ k)}) (snd g (~ i))

  jlp-unit-counit : (A : Pointed ℓA)
    → jlp-counit (∙join A B) ∘∙ join-mapₗ (jlp-unit A) ≡ idfun∙ (∙join A B)
  fst (jlp-unit-counit A i) (inl a) = (push (pt A) (pt B) ∙ sym (push a (pt B))) i
  fst (jlp-unit-counit A i) (inr b) = push (pt A) b i
  fst (jlp-unit-counit A i) (push a b j) = doubleCompPath-filler
    (push (pt A) (pt B) ∙ sym (push a (pt B))) (push a b) (sym (push (pt A) b)) (~ i) j
  snd (jlp-unit-counit A i) j = hcomp
    (λ k → λ { (i = i0) → doubleCompPath-filler {x = inl (pt A)} refl refl refl k j
             ; (i = i1) → push (pt A) (pt B) ((~ j) ∧ (~ k))
             ; (j = i0) → doubleCompPath-filler refl (push (pt A) (pt B))
                                                (sym (push (pt A) (pt B))) k i
             ; (j = i1) → inl (pt A)}) (push (pt A) (pt B) (i ∧ (~ j)))

  jlp-counit-unit : (X : Pointed ℓX)
    → lpmap-mapₗ (jlp-counit X) ∘∙ jlp-unit (B →∙ Ω X ∙)
    ≡ idfun∙ (B →∙ Ω X ∙)
  jlp-counit-unit X = →∙Homogeneous≡ (lpmap-homogeneous X) (funExt lemma₁)
    where
      lemma₁ : (f : B →∙ Ω X) → fst (lpmap-mapₗ (jlp-counit X) ∘∙ jlp-unit (B →∙ Ω X ∙)) f ≡ f
      lemma₁ f = →∙Homogeneous≡ (isHomogeneousΩ X) (funExt lemma₂)
        where
          lemma₂ : (b : typ B)
            → fst (fst (lpmap-mapₗ (jlp-counit X) ∘∙ jlp-unit (B →∙ Ω X ∙)) f) b ≡ fst f b
          lemma₂ b = conj-refl _ ∙ (
            cong (fst (jlp-counit X)) (τ (B →∙ Ω X ∙) B f b)
              ≡⟨ cong-∙∙ (fst (jlp-counit X)) (push c (pt B) ∙ sym (push f (pt B)))
                 (push f b) (sym (push c b)) ⟩
            (cong (fst (jlp-counit X)) (push c (pt B) ∙ sym (push f (pt B))))
              ∙∙ fst f b ∙∙ refl
              ≡⟨ cong (λ q → q ∙∙ fst f b ∙∙ refl) p₁  ⟩
            fst f b ∙ refl
              ≡⟨ sym (rUnit (fst f b)) ⟩
            fst f b ∎ )
            where
              c = pt (B →∙ Ω X ∙)
              p₁ : cong (fst (jlp-counit X)) (push c (pt B) ∙ sym (push f (pt B))) ≡ refl
              p₁ = cong-∙ (fst (jlp-counit X)) (push c (pt B)) (sym (push f (pt B)))
                ∙ sym (lUnit _) ∙ cong sym (snd f)

{-
  Alternatively, we can give a direct isomorphism:
  This is however slow to type-check.
-}
  module _ (A : Pointed ℓA) (X : Pointed ℓX) where
    private

      from : (A →∙ (B →∙ Ω X ∙)) → (∙join A B →∙ X)
      fst (from h) (inl a) = pt X
      fst (from h) (inr b) = pt X
      fst (from h) (push a b i) = h .fst a .fst b i
      snd (from h) = refl

    -- with this we can check the claim that we get the claimed map:
    ψ-path : (h : typ A → (∙Susp (typ B) →∙ X)) (a : typ A) (b : typ B)
      → Path (typ X) (pt X) (pt X)
    ψ-path h a b = conj (h a .snd) (cong (h a .fst) (σ B b ))

    ψ : (A →∙ (∙Susp (typ B) →∙ X ∙)) → (∙join A B →∙ X)
    fst (ψ (h , h∙)) (inl a) = pt X
    fst (ψ (h , h∙)) (inr b) = pt X
    fst (ψ (h , h∙)) (push a b i) = ψ-path h a b i
    snd (ψ (h , h∙)) = refl

    Φ : (∙Susp (typ B) →∙ X ∙) →∙ (B →∙ Ω X ∙)
    fst Φ = Iso.inv (LoopSuspIso B X)
    snd Φ = →∙Homogeneous≡ (isHomogeneousΩ X) (funExt λ b → sym (lUnit refl))

    φ : (A →∙ (∙Susp (typ B) →∙ X ∙)) → (∙join A B →∙ X)
    φ h = from (Φ ∘∙ h)

    check : φ ≡ ψ
    fst (check i h) (inl a) = pt X
    fst (check i h) (inr b) = pt X
    fst (check i h) (push a b j) = ψ-path (fst h) a b j
    snd (check i h) = refl

    -- we can also check that `from` really comes from the adjunction
    ξ : (A →∙ (B →∙ Ω X ∙)) → (∙join A B →∙ X)
    ξ h = jlp-counit X ∘∙ join-mapₗ h

    check₂ : ξ ≡ from
    fst (check₂ i h) (inl a) = pt X
    fst (check₂ i h) (inr b) = pt X
    fst (check₂ i h) (push a b j) = h .fst a .fst b j
    snd (check₂ i h) = sym (rUnit refl) i

{-
    -- Here comes the rest of the isomorphism
    private
      to : (∙join A B →∙ X) → (A →∙ (B →∙ Ω X ∙))
      fst (fst (to g) a) b = conj (snd g) (cong (fst g) (τ A B a b))
      snd (fst (to g) a) = cong (conj (snd g)) (cong (cong (fst g)) (τ-pt-r A B a))
        ∙ lCancelOuter (snd g)
      snd (to g) = →∙Homogeneous≡ (isHomogeneousΩ X)
        (funExt λ b → cong (conj (snd g)) (cong (cong (fst g)) (τ-pt-l A B b))
          ∙ lCancelOuter (snd g))

      to-from : section to from
      to-from h = →∙Homogeneous≡ (lpmap-homogeneous X) (funExt lemma₁)
        where
          lemma₁ : (a : typ A) → fst (to (from h)) a ≡ h .fst a
          lemma₁ a = →∙Homogeneous≡ (isHomogeneousΩ X) (funExt lemma₂)
            where
              lemma₂ : (b : typ B) → fst (fst (to (from h)) a) b ≡ h .fst a .fst b
              lemma₂ b = conj-refl (cong (fst (from h)) (τ A B a b)) ∙ sq
                where
                  p₁ : cong (fst (from h)) (push (pt A) (pt B) ∙ sym (push a (pt B))) ≡ refl
                  p₁ =
                    cong (fst (from h)) (push (pt A) (pt B) ∙ sym (push a (pt B)))
                      ≡⟨ cong-∙ (fst (from h)) (push (pt A) (pt B)) (sym (push a (pt B))) ⟩
                    h .fst (pt A) .fst (pt B) ∙ sym (h .fst a .fst (pt B))
                      ≡⟨ cong (λ q → h .fst (pt A) .fst (pt B) ∙ sym q) (h .fst a .snd) ⟩
                    h .fst (pt A) .fst (pt B) ∙ refl
                      ≡⟨ sym (rUnit _) ⟩
                    h .fst (pt A) .fst (pt B)
                      ≡⟨ (λ t → h .snd t .fst (pt B)) ⟩
                    refl ∎
                  sq : cong (fst (from h)) (τ A B a b) ≡ h .fst a .fst b
                  sq =
                    cong (fst (from h)) (τ A B a b)
                      ≡⟨ cong-∙∙ (fst (from h))
                      (push (pt A) (pt B) ∙ sym (push a (pt B)))
                      (push a b) (sym (push (pt A) b))  ⟩
                    cong (fst (from h)) (push (pt A) (pt B) ∙ sym (push a (pt B)))
                      ∙∙ cong (fst (from h)) (push a b)
                      ∙∙ cong (fst (from h)) (sym (push (pt A) b))
                      ≡⟨ cong (λ q → q ∙∙ h .fst a .fst b ∙∙ sym (h .fst (pt A) .fst b)) p₁  ⟩
                    h .fst a .fst b ∙ sym (h .fst (pt A) .fst b)
                      ≡⟨ cong (λ q → h .fst a .fst b ∙ sym q) (λ t → h .snd t .fst b) ⟩
                    h .fst a .fst b ∙ refl
                      ≡⟨ sym (rUnit _) ⟩
                    h .fst a .fst b ∎

      from-to : retract to from
      fst (from-to g i) (inl a) = (sym (snd g) ∙∙
        cong (fst g) (push (pt A) (pt B) ∙ (sym (push a (pt B)))) ∙∙ refl) i
      fst (from-to g i) (inr b) = ((sym (snd g)) ∙∙ cong (fst g) (push (pt A) b) ∙∙ refl) i
      fst (from-to g i) (push a b j) = hcomp
        (λ k → λ { (i = i0) → doubleCompPath-filler (sym (snd g))
                      (cong (fst g) (τ A B a b)) (snd g) k j
                 ; (i = i1) → fst g (push a b j)
                 ; (j = i0) → doubleCompPath-filler (sym (snd g))
                      (cong (fst g) (push (pt A) (pt B) ∙ (sym (push a (pt B))))) refl k i
                 ; (j = i1) → doubleCompPath-filler (sym (snd g))
                      (cong (fst g) (push (pt A) b)) refl k i })
        (fst g (doubleCompPath-filler (push (pt A) (pt B) ∙ (sym (push a (pt B))))
                                      (push a b) (sym (push (pt A) b)) (~ i) j) )
      snd (from-to g i) j = hcomp
        (λ k → λ { (i = i0) → snd g k
                 ; (i = i1) → snd g (j ∧ k)
                 ; (j = i0) → doubleCompPath-filler (sym q) (cong (fst g) (p ∙ sym p)) refl k i
                 ; (j = i1) → snd g k}) (cong (cong (fst g)) (rCancel p) j i)
        where
          p = push (pt A) (pt B)
          q = snd g

    jlp-iso : Iso (∙join A B →∙ X) (A →∙ (B →∙ Ω X ∙))
    Iso.fun jlp-iso = to
    Iso.inv jlp-iso = from
    Iso.rightInv jlp-iso = to-from
    Iso.leftInv jlp-iso = from-to
-}
