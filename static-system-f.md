# System F with representation polymorphism

This is meant to be an *internal* language, produced via an elaboration
step from surface OCaml.

    ϕ ::= s | d             Phases
    e, f ::=                Terms
      | x                   Variable with phase
      | fun (x :_ϕ τ) -> e  Term abstraction
      | e e                 Normal application
      | e · e               Specialization
      | Fun (α : κ) -> e    Type abstraction
      | e[τ]                Type application
      | FUN (ξ <: κ) -> e   Kind abstraction
      | e{κ}                Kind application
      | ⌈e⌉                 Lift to dynamic
    τ, σ ::=                Types
      | α                   Type variable
      | τ ->_ϕ τ            Function
      | ∀ (α : κ) -> τ      Polymorphic function
      | ∀ (ξ <: κ) -> τ     Kind-polymorphic function
      | ...                 Base types
    K ::=                   Base kinds
      | any                 Top kind
      | C                   Concrete kind
    C ::=                   Concrete kinds
      | value               Value kind
      | float64             64-bit floats
      | ...                 Base kinds
    κ ::=                   Kinds
      | ξ                   Kind variable
      | K                   Base kind
    Δ ::=                   Kind contexts
      | ∅                   Empty
      | Δ, ξ <: κ           Kind variable
    Σ ::=                   Type contexts
      | ∅                   Empty
      | Σ, α : κ            Type variable
    Γ ::=                   Term contexts
      | ∅                   Empty
      | Γ, x :_ϕ τ          Term variable

All contexts should be viewed as sets and allow arbitrary well-scoped
permutation.

## Typing rules for kinds

    Δ ⊢ κ layout ::=

    Δ ⊢ κ layout
    -------------------- (Var)
    Δ, ξ <: κ ⊢ ξ layout

    ------------ (Base)
    Δ ⊢ K layout

A kind κ for which `Δ ⊢ κ layout` holds describes a runtime layout for types.
If `Δ ⊢ κ layout` does *not* hold and if `τ : κ`, then it is non-sensical to
have any expression `e` such that `e : τ`.

In OCaml, without higher-order kinds, *all* kinds describe layouts, as we
see in the Layout axiom above. In a language with higher-order kinds, not
all kinds will be layouts. We include `layout` premises below to suggest
where checks might be needed in a more elaborate language.

    Δ ⊢ κ concrete ::=

    Δ ⊢ κ concrete
    ------------------ (Var)
    Δ, ξ <: κ concrete

    -------------- (Concrete)
    Δ ⊢ C concrete

This unary relation, `concrete`, checks whether a layout has enough information
to actually be compiled. Notably, `Δ ⊢ any concrete` does *not* hold.

## Subtyping for kinds

There is a subtype relation on kinds.

    Δ ⊢ κ₁ <: κ₂ ::=

    ------------------ (Var)
    Δ, ξ <: κ ⊢ ξ <: κ

    fv(κ) ⊆ dom(Δ)
    -------------- (Any)
    Δ ⊢ κ <: any

    fv(κ) ⊆ dom(Δ)
    -------------- (Refl)
    Δ ⊢ κ <: κ

    Δ ⊢ κ₁ <: κ₂
    Δ ⊢ κ₂ <: κ₃
    ------------ (Trans)
    Δ ⊢ κ₁ <: κ₃

## Typing rules for types

    Δ; Σ ⊢ τ : κ ::=

    ------------------- (TyVar)
    Δ; Σ, α : κ ⊢ α : κ

    Δ; Σ ⊢ τ₁ : κ₁
    Δ ⊢ κ₁ layout
    Δ; Σ ⊢ τ₂ : κ₂
    Δ ⊢ κ₂ layout
    ------------------------------ (Arrow)
    Δ; Σ ⊢ τ₁ ->_ϕ τ₂ : value

    fv(κ₁) ⊆ dom(Δ)
    Δ; Σ, α : κ₁ ⊢ τ : κ₂
    Δ ⊢ κ₂ layout
    -------------------------- (ForAll)
    Δ; Σ ⊢ ∀ (α : κ₁) -> τ : κ₂

    fv(κ₁) ⊆ dom(Δ)
    Δ, ξ <: κ₁; Σ ⊢ τ : κ₂
    Δ ⊢ κ₂ layout
    ---------------------------- (KForAll)
    Δ; Σ ⊢ ∀ (ξ <: κ₁) -> τ : κ₂

    Δ; Σ ⊢ τ : κ₁
    Δ ⊢ κ₁ <: κ₂
    ------------- (Sub)
    Δ; Σ ⊢ τ : κ₂

## Typing rules for terms

    Δ; Σ; Γ ⊢ e :_ϕ τ ::=

    -------------------------- (Var)
    Δ; Σ; Γ, x :_ϕ τ ⊢ x :_ϕ τ

    Δ; Σ; Γ ⊢ e :_s τ
    ----------------- (Lift)
    Δ; Σ; Γ ⊢ ⌈e⌉ :_d τ

    Δ; Σ ⊢ τ₁ : κ
    Δ ⊢ κ layout
    Δ; Σ; Γ, x :_ϕ τ₁ ⊢ e :_s τ₂
    -------------------------------------------- (Lam-S)
    Δ; Σ; Γ ⊢ fun (x :_ϕ τ₁) -> e :_s τ₁ ->_ϕ τ₂

    Δ; Σ ⊢ τ₁ : κ
    Δ ⊢ κ concrete
    Δ; Σ; Γ, x :_ϕ τ₁ ⊢ e :_d τ₂
    -------------------------------------------- (Lam-D)
    Δ; Σ; Γ ⊢ fun (x :_ϕ τ₁) -> e :_d τ₁ ->_ϕ τ₂

    Δ; Σ; Γ ⊢ f :_s τ₁ ->_s τ₂
    Δ; Σ; Γ ⊢ e :_s τ₁
    ----------------------------------------- (App-S-S)
    Δ; Σ; Γ ⊢ f e :_s τ₂

    Δ; Σ; Γ ⊢ f :_d τ₁ ->_d τ₂
    Δ; Σ; Γ ⊢ e :_d τ₁
    Δ; Σ ⊢ τ₁ : κ
    Δ ⊢ κ concrete
    --------------------------------------------------- (App-D-D)
    Δ; Σ; Γ ⊢ f e :_d τ₂

    fv(κ) ⊆ dom(Δ)
    Δ; Σ, α : κ; Γ ⊢ e :_ϕ τ
    --------------------------------------------- (TyLam)
    Δ; Σ; Γ ⊢ Fun (α : κ) -> e :_ϕ ∀ (α : κ) -> τ

    Δ; Σ; Γ ⊢ f :_ϕ ∀ (α : κ) -> τ₂
    Δ; Σ ⊢ τ₁ : κ
    ----------------------------------------------- (TyApp)
    Δ; Σ; Γ ⊢ f[τ₁] :_ϕ τ₂{τ₁/α}

    fv(κ) ⊆ dom(Δ)
    Δ, ξ <: κ; Σ; Γ ⊢ e : τ
    --------------------------------------------- (KiLam)
    Δ; Σ; Γ ⊢ FUN (ξ <: κ) -> e : ∀ (ξ <: κ) -> τ

    Δ; Σ; Γ ⊢ e : ∀ (ξ <: κ₂) -> τ
    Δ ⊢ κ <: κ₂
    ------------------------------ (KiApp)
    Δ; Σ; Γ ⊢ e{κ} : τ{κ/ξ}

    Δ; Σ; Γ ⊢ f :_s τ₁ ->_d τ₂
    Δ; Σ; Γ ⊢ e :_d τ₁
    ----------------------------------------------- (Spec)
    Δ; Σ; Γ ⊢ f · e :_d τ₂

## The static computation operator `⌊-⌋`

The important theorem we want is:

  **Theorem 1.** If `∅ ⊢ e :_s τ` then `∅ ⊢ ⌊e⌋ :_d τ`.

(Probably we can let the context be non-empty as well, if we define `⌊Γ⌋` as
"make all the variables dynamic," but the important case is a closed term.)

I'm not entirely sure how best to define `⌊-⌋`. Probably it will have to be
composed from two relations/functions: one to do all the static computation,
then one to change every remaining `∀ α : any` to `∀ α : value`. (Doing them at
the same time would be a problem: if we define `⌊-⌋` using a big-step
operational semantics in the usual way, then `⌊ f[int64] ⌋` gets stuck because
`⌊f⌋` can't be applied to `int64`.)

If we decompose `⌊e⌋` as `lower (compute e)` where `compute` applies as many
static reductions as possible and then `lower` goes through and changes every
occurrence of `any` into `value`, then our theorem comes down to

  1. Subject reduction (`compute` doesn't change types)
  2. Safety of lowering (`lower` on a statically-normal form changes types
     consistently)

(Does `⌈e⌉` implicitly perform `lower` on `e`? It has to, right? Otherwise I can
have dynamic variables with kind-polymorphic argument types running around, and
also Theorem 1 doesn't hold, at least without changing `τ` to `⌊τ⌋` in the
conclusion. Wait, no, `lower` doesn't help, since `⌈f⌉` can only be just `f`,
which can still have a naughty type. Unless `⌈-⌉` is defined by recursion on the
type, TDPE-style, so that `⌈f⌉` might become `Fun (α : value) -> ⌈ f[α] ⌉` by
definition or reduction or something.)
