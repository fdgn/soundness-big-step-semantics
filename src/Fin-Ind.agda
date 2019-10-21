open import Data.Nat as ℕ  using (ℕ)
open import Data.Fin
open import Induction.WellFounded as WF
open import Induction.Nat
open import Relation.Binary.PropositionalEquality

<-Fin : ∀ {n} → (k : Fin n) → toℕ k ℕ.< n
<-Fin zero = ℕ.s≤s ℕ.z≤n
<-Fin (suc k) = ℕ.s≤s (<-Fin k)

≡-to-fromℕ : ∀ {n} → ∀ k → (k<n : k ℕ.< n) → toℕ (fromℕ≤ k<n) ≡ k
≡-to-fromℕ ℕ.zero (ℕ.s≤s ℕ.z≤n) = refl
≡-to-fromℕ (ℕ.suc k) (ℕ.s≤s (ℕ.s≤s k<n)) = cong (λ i → ℕ.suc i) (≡-to-fromℕ k (ℕ.s≤s k<n))

<-fin-nat : ∀ {n} → (j : Fin n) → ∀ k → (k<n : k ℕ.< n) → j < fromℕ≤ k<n → (toℕ j) ℕ.< k
<-fin-nat j k k<n j<k = subst (λ k → toℕ j ℕ.< k) (≡-to-fromℕ k k<n) j<k

≡-from-to-ℕ : ∀ {n} → (k : Fin n) → fromℕ≤ (<-Fin k) ≡ k
≡-from-to-ℕ zero = refl
≡-from-to-ℕ (suc zero) = refl
≡-from-to-ℕ (suc (suc k)) = cong (λ i → suc i) (≡-from-to-ℕ (suc k))

Fin-rec-ℕ : ∀ {n} → (P : Fin n → Set) →
            (∀ i → (∀ j → j < i → P j) → P i) →
            ∀ k → (∀ h → h ℕ.< k → (h<n : h ℕ.< n) → P (fromℕ≤ h<n)) → (k<n : k ℕ.< n) → P (fromℕ≤ k<n)
Fin-rec-ℕ P fin-ind k nat-ind k<n = fin-ind (fromℕ≤ k<n) λ j j<k → subst P (≡-from-to-ℕ j)
                                                          (nat-ind (toℕ j) (<-fin-nat j k k<n j<k) (<-Fin j) )

Fin-ind : ∀ {n} → (P : Fin n → Set) →
          (∀ i → (∀ j → j < i → P j) → P i) →
          ∀ i → P i
Fin-ind {n} P ind i = subst P (≡-from-to-ℕ i)
                      ((<-rec (λ k → (k<n : k ℕ.< n) → P (fromℕ≤ k<n)) (Fin-rec-ℕ P ind)) (toℕ i) (<-Fin i))
