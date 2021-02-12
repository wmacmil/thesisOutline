{-# OPTIONS --cubical #-}

module Monoid where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude renaming (_∙_ to _∙''_)
open import Cubical.Foundations.Isomorphism
-- open import Cubical.Data.Sigma
-- open import Cubical.Data.Nat -- using (ℕ ; zero ; suc ; _+_ ; _*_; isSetℕ; *-distribˡ; injSuc; inj-m+ ; +-zero; snotz; 0≡m*0)
-- open import Cubical.Data.Empty
-- open import Cubical.Data.Unit.Base
-- open import Cubical.Data.Unit.Properties

-- ctrl x 1
-- ctrl x 3
--ctrl x f 80 set-fill column
--toggle fill column indicator

-- a : ℕ

private
  variable
    ℓ : Level

is-left-unit-for : {A : Type ℓ} → A → (A → A → A) → Type ℓ
is-left-unit-for {A = A} e _⋆_ = (x : A) → e ⋆ x ≡ x

is-right-unit-for : {A : Type ℓ} → A → (A → A → A) → Type ℓ
is-right-unit-for {A = A} e _⋆_ = (x : A) → x ⋆ e ≡ x

is-assoc : {A : Type ℓ} → (A → A → A) → Type ℓ
is-assoc {A = A} _⋆_ = (x y z : A) → (x ⋆ y) ⋆ z ≡ x ⋆ (y ⋆ z)


record MonoidStrRec (A : Type ℓ) : Type ℓ where
  constructor
    monoid
  field
    ε   : A
    _∙_ : A → A → A

    left-unit  : is-left-unit-for ε _∙_
    right-unit : is-right-unit-for ε _∙_
    assoc      : is-assoc _∙_

    carrier-set : isSet A

record Monoid' : Type (ℓ-suc ℓ) where
  constructor
    monoid'
  field
    A : Type ℓ
    ε   : A
    _∙_ : A → A → A

    left-unit  : is-left-unit-for ε _∙_
    right-unit : is-right-unit-for ε _∙_
    assoc      : is-assoc _∙_

    carrier-set : isSet A

monoidHom : {ℓ : Level} → ((monoid' a _ _ _ _ _ _) (monoid' a' _ _ _ _ _ _) : Monoid' {ℓ} ) → (a → a') → Type ℓ
monoidHom (monoid' A ε _∙_ left-unit right-unit assoc carrier-set) (monoid' A₁ ε₁ _∙₁_ left-unit₁ right-unit₁ assoc₁ carrier-set₁) f
  = (m1 m2 : A) → f (m1 ∙ m2) ≡ (f m1) ∙₁ (f m2)

-- record Category {ℓ : Level} : Type (ℓ-suc ℓ) where
--   field
--     Obj  : Type ℓ
--     _=>_ : Obj → Obj → Type ℓ
--     id=> : {T : Obj} → T => T
--     _∘_  : {R S T : Obj} → R => S → S => T → R => T
--     lunit : {S T : Obj} (f : S => T) → (id=> {S} ∘ f) ≡ f
--     runit : {S T : Obj} (f : S => T) → (f ∘ id=> {T}) ≡ f
--     assoc : {Q R S T : Obj} (f : Q => R)(g : R => S)(h : S => T) ->
--       ((f ∘ g) ∘ h) ≡ (f ∘ (g ∘ h))

--     setObj : isSet Obj

-- -- -- depunCurry : {A : Set} {B : A → Set} {C : (a : A) → B a → Set} → ((a : A) → (b : B a) → ((a' : A) (b' : B a') → C a' b')) → Σ[ a ∈ A ] (B a) → ((a' : A) (b' : B a') → C a' b')
-- -- depunCurry : {A : Set} {B : A → Set} {C : (a : A) → B a → Set} → ((a : A) → (b : B a) → ((a' : A) (b' : B a') → C a' b')) → Σ[ a ∈ A ] (B a) → ((a' : A) (b' : B a') → C a' b')
-- -- depunCurry {A} {C} {B} f (fs , sn) = λ a' b' → f fs sn a' b' 

-- depunCurry : {A C : Set} {B : A → Set} → ((a : A) → B a → C) → Σ[ a ∈ A ] (B a) → C 
-- depunCurry {A} {C} {B} f (fs , sn) = f fs sn

-- depCurry : {A C : Set} {B : A → Set} → (Σ[ a ∈ A ] (B a) → C) → (a : A) → B a → C
-- depCurry f a ba = f (a , ba)

-- -- this is just a curried version of what's written below
-- -- what about the is-set part?
-- mon2Cat : (A : Type ℓ-zero) (ε' : A) (∙' : A → A → A) → (lu : is-left-unit-for ε' ∙' ) (ru : is-right-unit-for ε' ∙')
--   (asoc : is-assoc ∙') (s : isSet A) → Category {ℓ-zero}
-- mon2Cat A ε' ∙' lu ru asoc s = 
--   record
--     { Obj = Unit
--     ; _=>_ = λ _ _ → A
--     ; id=> = ε'
--     ; _∘_ = λ x x₁ → ∙' x x₁
--     ; lunit = lu -- λ a → left-unit a
--     ; runit = ru
--     ; assoc = asoc
--     ; setObj = isSetUnit
--     }

-- monToCat : Monoid' {ℓ-zero} → Category {ℓ-zero}
-- monToCat (monoid' A ε _∙_ left-unit right-unit assoc carrier-set) =
--   record
--     { Obj = Unit
--     ; _=>_ = λ _ _ → A
--     ; id=> = ε
--     ; _∘_ = λ x x₁ → x ∙ x₁
--     ; lunit = left-unit -- λ a → left-unit a
--     ; runit = right-unit
--     ; assoc = assoc
--     ; setObj = isSetUnit
--     }

-- mon2ToCat : Monoid' {ℓ-zero} → Category {ℓ-zero}
-- mon2ToCat (monoid' A ε _∙_ left-unit right-unit assoc carrier-set) = mon2Cat A ε _∙_ left-unit right-unit assoc carrier-set

-- monoidHom : {ℓ : Level} → ((monoid' a _ _ _ _ _ _) (monoid' a' _ _ _ _ _ _) : Monoid' {ℓ} ) → (a → a') → Type ℓ
-- monoidHom (monoid' A ε _∙_ left-unit right-unit assoc carrier-set) (monoid' A₁ ε₁ _∙₁_ left-unit₁ right-unit₁ assoc₁ carrier-set₁) f
--   = (m1 m2 : A) → f (m1 ∙ m2) ≡ (f m1) ∙₁ (f m2)


-- MonoidStrΣ : Type ℓ → Type ℓ
-- MonoidStrΣ A =
--   Σ[ ε ∈ A ] Σ[ _∙_ ∈ (A → A → A) ]
--   (is-left-unit-for ε _∙_ × is-right-unit-for ε _∙_ × is-assoc _∙_ × isSet A)

-- MonoidRec : (ℓ : Level) → Type (ℓ-suc ℓ)
-- MonoidRec l = Σ[ A ∈ Type l ] MonoidStrRec A

-- MonoidΣ : (ℓ : Level) → Type (ℓ-suc ℓ)
-- MonoidΣ l = Σ[ A ∈ Type l ] MonoidStrΣ A

-- ℕMonoidRec : MonoidRec ℓ-zero
-- ℕMonoidRec = ℕ , monoid 0 _+_ li  rid assoc-ℕ set-ℕ
--   where
--     li : is-left-unit-for 0 _+_
--     li zero = λ i → 0
--     li (suc x) = λ i → suc x
--     rid : is-right-unit-for 0 _+_
--     rid zero = λ i → 0
--     rid (suc x) = cong suc (λ i → rid x i) --  λ i → rid x {!i!}
--     assoc-ℕ : is-assoc _+_
--     assoc-ℕ zero y z = λ i → y + z
--     assoc-ℕ (suc x) y z = cong suc (λ i → assoc-ℕ x y z i)
--     set-ℕ : isSet ℕ
--     set-ℕ = isSetℕ

-- ℕMonoid' : Monoid'
-- ℕMonoid' = monoid' ℕ 0 _+_ li  rid assoc-ℕ isSetℕ -- set-ℕ
--   where
--     li : is-left-unit-for 0 _+_
--     li zero = refl --λ i → 0
--     li (suc x) = λ i → suc x
--     rid : is-right-unit-for 0 _+_
--     rid zero = refl --λ i → 0
--     rid (suc x) = cong suc (λ i → rid x i) --  λ i → rid x {!i!}
--     assoc-ℕ : is-assoc _+_
--     assoc-ℕ zero y z = refl -- λ i → y + z
--     assoc-ℕ (suc x) y z = cong suc (assoc-ℕ x y z)
--     -- set-ℕ : isSet ℕ
--     -- set-ℕ = isSetℕ

-- natCat : Category
-- natCat = monToCat ℕMonoid'

-- -- 0' : ℕ
-- -- 0' = natCat._=>_

-- CatObj : {ℓ : Level} → Category {ℓ} → Type ℓ
-- CatObj c = Category.Obj c

-- 0' : ℕ
-- 0' = Category.id=> natCat

-- natCatarr' : {ℓ : Level} → Type ℓ-zero
-- natCatarr' = Category._=>_  natCat tt tt

-- asdf : {ℓ : Level} → natCatarr' {ℓ} → ℕ
-- asdf zero = zero
-- asdf (suc x) = x

-- f : Level → ℕ
-- f l = asdf {l} 2

-- -- f' = Category._∘_ natCat 0' (Category._=>_  natCat tt tt) -- f ℓ-zero 

-- recover0 : 0' ≡ 0
-- recover0 = refl --λ i → zero

-- ⊤' : Set
-- ⊤' = CatObj natCat

-- 0+ : ℕ → ℕ
-- 0+ n = 0 + n

-- idNat : monoidHom ℕMonoid' ℕMonoid'  0+
-- idNat m1 m2 = refl

-- -- partially evaluated * fcn
-- n* : ℕ → ℕ → ℕ
-- n* n m = n * m

-- *nHom : (n : ℕ) → monoidHom ℕMonoid' ℕMonoid' (n* n)
-- *nHom n m1 m2 = sym (*-distribˡ n m1 m2)

-- 0prop : (a : ℕ) → a ≡ a + a → a ≡ 0
-- 0prop zero p = refl
-- 0prop (suc a) p = rec (snotz contra)
--   where
--     lem1 : a ≡ a + suc a
--     lem1 = injSuc p
--     contra : (suc a) ≡ 0
--     contra = inj-m+ (sym lem1 ∙'' sym (+-zero a))

-- classifyNatHoms : (f : ℕ → ℕ) → monoidHom ℕMonoid' ℕMonoid' f → Σ[ n ∈ ℕ ] (f ≡ (n* n))
-- classifyNatHoms f fhom = f 1 , funExt f=n*
--   where
--     f=n* : (n : ℕ) → f n ≡ (n* (f 1) n) -- how to prevent this inference? PathP (λ _ → ℕ) (f n) (n* (f 1) n)
--     f=n* zero =
--       f zero ≡⟨ 0prop (f 0) (fhom 0 0) ⟩
--       zero   ≡⟨ 0≡m*0 (f 1) ⟩
--       f 1 * zero ∎
--       -- f 1 * zero ∎
--     f=n* (suc n) =
--       f (1 + n)     ≡⟨ fhom 1 n  ⟩
--       f 1 + f n     ≡⟨ cong (λ a → (f 1) + a) (f=n* n) ⟩
--       f 1 + f 1 * n ≡⟨ sym (*-suc (f 1) (n)) ⟩
--       f 1 * suc n ∎


-- -- isMonoidHom : {ℓ : Level} → (m1 m2 : MonoidRec {ℓ} ) → (MonoidRec.A m1  → MonoidRec'.A m2) → Type ℓ -- (ℓ-suc ℓ)
-- -- isMonoidHom (monoid' A' ε _∙_ left-unit right-unit assoc carrier-set) (monoid' A₁' ε₁ _∙₁_ left-unit₁ right-unit₁ assoc₁ carrier-set₁) f = (x y : A) → f (x ∙ y) ≡ ((f x) ∙₁ (f y))
-- --   where
-- --     open MonoidRec'
-- --   --   open MonoidRec' m2

-- ∣_∣ : MonoidΣ ℓ → Type ℓ
-- ∣_∣ = fst

-- str-mon : (m : MonoidΣ ℓ) → MonoidStrΣ ∣ m ∣
-- str-mon = snd


-- to : {ℓ : Level} → MonoidRec ℓ → MonoidΣ ℓ
-- to (A , ms) = A , ε  , _∙_ , left-unit , right-unit , assoc , carrier-set
--   where
--     open MonoidStrRec ms

-- from : {ℓ : Level} → MonoidΣ ℓ → MonoidRec ℓ
-- from (A , e , _∙_ , lu , ru , asc , cs ) =
--   A , monoid e _∙_ lu ru asc cs

-- sec : {ℓ : Level} → section (to {ℓ}) (from {ℓ})
-- sec (A , e , _∙_ , lu , ru , asc , cs ) = refl -- λ i → A , (e , (_∙_ , lu , (ru , (asc , cs))))

-- retr : {ℓ : Level} → retract  (to {ℓ}) (from {ℓ})
-- retr (A , monoid ε _∙_ left-unit right-unit assoc carrier-set) = refl

-- MonsEquiv : {ℓ : Level} →  MonoidRec ℓ ≃ MonoidΣ ℓ 
-- MonsEquiv = isoToEquiv (iso to from sec retr)

-- -- module FUNCTOR where
-- --   open Category
-- --   record _≡>_ (C D : Category) : Type {!!} where  -- "junctor from C to D"m1
-- --     field
-- --       F₀ : Obj C -> Obj D
-- --       F₁ : {S T : Obj C} -> _=>_ C S T -> _=>_ D (F₀ S) (F₀ T)
-- --       F-id : {S : Obj C} → F₁ (id=> C {S}) ≡ id=> D -- {F₀ S}
-- --       F-hom : {S T U : Obj C} (f : _=>_ C S T) (g : _=>_ C T U) → F₁ (_∘_ C f g) ≡ _∘_ D (F₁ f) (F₁ g)  

-- -- open FUNCTOR public



-- --alt comma, right control comma

-- -- equivMon : (ℓ : Level) → MonoidRec ℓ → MonoidΣ ℓ
-- --   where
