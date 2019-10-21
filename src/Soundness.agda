open import Data.Fin using (Fin ; _<_ ; fromℕ)
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import NEList

module Soundness (C R : Set) where
  open import BSS C R
  open Rule
  open BSS

-- indexed predicates
  record Pred (I : Set) : Set₁ where
    constructor [_,_]
    field
      PC : I → C → Set
      PR : I → R → Set


    PConf : I → Conf → Set
    PConf i (conf c) = PC i c
    PConf i (res r) = PR i r

  -- Local preservation
    RS1 : Rule → Set
    RS1 ru =  ∀ {i} → ∀ {ctx : ru .Ctx} → PC i (cons ru ctx) →
              Σ[ f ∈ (Fin (len (prems ru ctx)) → I) ] (f (lastIdx (prems ru ctx)) ≡ i) ×
              (∀ {k} → (∀ {j} → j < k → PR (f j) (pr-res ru ctx j)) → PConf (f k) (pr-conf ru ctx k))

    S1 : BSS → Set
    S1 s = (rn : s .RId) → RS1 (s .rules rn)

    SR : Conf → R → Set
    SR c r = ∀ {i} → PConf i c → PR i r
  open Pred

  open import Fin-Ind

-- preservasion a.k.a. subject reduction
-- Lemma 1
-- If P holds for the conclusion and SR holds for all premises,
-- then P holds for all configurations in premises
  P-prems : ∀ {I} → (P : Pred I) → (ru : Rule) → (rs1 : RS1 P ru) →
            ∀ {ctx i} → (p-cons : P .PC i (cons ru ctx)) → (∀ {k} → SR P (pr-conf ru ctx k) (pr-res ru ctx k)) →
            ∀ k → PConf P (proj₁ (rs1 p-cons) k) (pr-conf ru ctx k)
  P-prems P ru rs1 {ctx} p-cons SR-prems = Fin-ind (λ k → PConf P (proj₁ (rs1 p-cons) k) (pr-conf ru ctx k))
                                            λ k ind → (proj₂ (proj₂ (rs1 p-cons))) λ {j} j<k → SR-prems (ind j j<k)

-- Lemma 2
-- If a BSS satisfies S1,
-- then SR is closed w.r.t. all rules in such BSS
  SR-closed : ∀ {I} → (P : Pred I) → (s : BSS) →
              S1 P s → ∀ {rn} → RClosed (s .rules rn)  (SR P)
  SR-closed P s P-s1 {rn} {ctx} sd SR-prems P-c = subst (λ i → P .PR i (rule-res (s .rules rn) ctx))
                                                      (proj₁ (proj₂ (P-s1 rn P-c)))
                                                      (SR-prems (P-prems P (s .rules rn) (P-s1 rn) P-c SR-prems (cont-id (s .rules rn))))

-- Theorem
-- If a BSS satisfies S1,
-- then SR holds for all derivable judgements
  S1-preservation : ∀ {I} → (P : Pred I) → (s : BSS) →
                    S1 P s →
                    ∀ {c r} → ⟦ s ⟧ c r → SR P c r
  S1-preservation P s P-s1 c=>r = [ s ]-ind (SR P) ((λ P-r → P-r) , (SR-closed P s P-s1 )) c=>r
