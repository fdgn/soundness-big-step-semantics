open import Data.Nat
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Vec using (Vec ; lookup ; []) renaming ( _∷_ to cons )

module NEList where
  data NEList (A : Set) : Set where
    _end : A → NEList A
    _∷_  : A → NEList A → NEList A

  len : ∀ {A} → NEList A → ℕ
  len (x end) = 1
  len (x ∷ l) = 1 + (len l)

  get : ∀ {A} → (l : NEList A) → Fin (len l) → A
  get (x end) zero = x
  get (x end) (suc ())
  get (x ∷ l) zero = x
  get (x ∷ l) (suc i) = get l i

  lastIdx : ∀ {A} → (l : NEList A) → Fin (len l)
  lastIdx (x end) = zero
  lastIdx (x ∷ l) = suc (lastIdx l)

  last : ∀ {A} → NEList A → A
  last l =  get l (lastIdx l)

  toVec : ∀ {A} → (l : NEList A) → Vec A (len l)
  toVec (x end) = cons x []
  toVec (x ∷ l) = cons x (toVec l)
