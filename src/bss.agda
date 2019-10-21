open import Data.Product
open import Data.Fin using (Fin ; fromℕ)
open import Data.Nat using (ℕ ; pred)
open import Agda.Builtin.Equality
open import Data.Empty

module BSS (C R : Set) where
  open import NEList

-- extended configurations
  data Conf : Set where
    conf : C → Conf
    res  : R → Conf

  record Rule : Set₁ where
    constructor rule-cons
    field
      Ctx   : Set
      comp  : Ctx → NEList (Conf × R) × C × Set

-- getters
    cons  : Ctx → C -- consequence configuration
    cons ctx = proj₁ (proj₂ (comp ctx))

    prems : Ctx → NEList (Conf × R) -- list of premises
    prems ctx = proj₁ (comp ctx)

    side  : Ctx → Set -- side condition
    side ctx = proj₂ (proj₂ (comp ctx))

    pr-conf : (ctx : Ctx) → Fin (len (prems ctx)) → Conf -- Configuration i-th premise
    pr-conf ctx i = proj₁ (get (prems ctx) i)

    pr-res : (ctx : Ctx) → Fin (len (prems ctx)) → R -- result i-th premise
    pr-res ctx i = proj₂ (get (prems ctx) i)

    cont : Ctx → Conf  -- continuation
    cont ctx = proj₁ (last (prems ctx))

    rule-res : Ctx → R -- consequence result
    rule-res ctx = proj₂ (last (prems ctx))

    cont-id : {ctx : Ctx} → Fin (len (proj₁ (comp ctx)))
    cont-id {ctx} = lastIdx (prems ctx)

-- semantics
    step : (Conf → R → Set) → C → R → Set
    step J c r = Σ[ ctx ∈ Ctx ] (c ≡ cons ctx) × (r ≡ rule-res ctx) × (side ctx) × (∀ {i} → J (pr-conf ctx i) (pr-res ctx i))

    RClosed : (Conf → R → Set) → Set
    RClosed J = ∀ {ctx} → side ctx → (∀ {i} → J (pr-conf ctx i) (pr-res ctx i)) → J (conf (cons ctx)) (rule-res ctx)
  open Rule using (step ; RClosed)

  syntax rule-cons Ctx (λ ctx → comp) = rule[ ctx ∈ Ctx ] comp

-- Big step semantics
  record BSS : Set₁ where
    field
      RId : Set
      rules : RId → Rule

    FSem : (Conf → R → Set) → Conf → R → Set
    FSem J (conf c) r = Σ[ rn ∈ RId ] step (rules rn) J c r
    FSem J (res r') r = r' ≡ r

    SClosed : (Conf → R → Set) → Set
    SClosed J = (∀ {r} → J (res r) r) × (∀ {rn} → RClosed (rules rn) J)
  open BSS using (FSem ; SClosed)

-- inductive interpretation of a BSS
  data ⟦_⟧ (s : BSS) : Conf → R → Set where
    fold : ∀ {c r} → FSem s (⟦ s ⟧) c r → ⟦ s ⟧ c r

  [_]-ind : (s : BSS) → (J : Conf → R → Set) →
            SClosed s J →
            ∀ {c r} → ⟦ s ⟧ c r → J c r
  [ s ]-ind J (Jr , rcl) {conf .(Rule.cons (BSS.rules s rn) ctx)} {.(proj₂ (last (Rule.prems (BSS.rules s rn) ctx)))}
                          (fold (rn , ctx , refl , refl , sd , pr)) = rcl {rn} sd (λ {i} → [ s ]-ind J (Jr , rcl) (pr {i}))
  [ s ]-ind J cl {res r}  {r} (fold refl) = proj₁ cl
