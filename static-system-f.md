# System F with staging

    ϕ ::= s | d             Phases
    e, f ::=                Terms
      | x_ϕ                 Variable with phase
      | fun (x_ϕ : τ) -> e  Term abstraction
      | e e                 Normal application
      | e · e               Specialization
      | Fun (α : κ) -> e    Type abstraction
      | e[τ]                Type application
      | ⌈e⌉                 Lift to dynamic
    τ, σ ::=                Types
      | α                   Type variable
      | τ ->_ϕ τ            Function
      | ∀ (α : κ) -> τ      Polymorphic function
      | ...                 Base types
    κ ::=                   Kinds
      | any                 Top kind
      | value               Value kind
      | ...                 Base kinds
    Σ ::=                   Type contexts
      | ∅                   Empty
      | Σ, α : κ            Type variable
    Γ ::=                   Term contexts
      | ∅                   Empty
      | Γ, x : τ            Term variable

## Typing rules for kinds

    -------- (Layout)
    κ layout

A kind κ for which `κ layout` holds describes a runtime layout for types.
If `κ layout` does *not* hold and if `τ : κ`, then it is non-sensical to
have any expression `e` such that `e : τ`.

In OCaml, without higher-order kinds, *all* kinds describe layouts, as we
see in the Layout axiom above. In a language with higher-order kinds, not
all kinds will be layouts. We include `layout` premises below to suggest
where checks might be needed in a more elaborate language.

## Subtyping for kinds

There is a subtype relation on kinds.

    -------- (Any)
    κ <: any

    ------ (Refl)
    κ <: κ

    κ₁ <: κ₂
    κ₂ <: κ₃
    -------- (Trans)
    κ₁ <: κ₃

## Typing rules for types

    ---------------- (TyVar)
    Σ, α : κ ⊢ α : κ

    Σ ⊢ τ₁ : κ₁   κ₁ layout
    Σ ⊢ τ₂ : κ₂   κ₂ layout
    -------------------------- (Arrow)
       Σ ⊢ τ₁ -> τ₂ : value

    Σ, α : κ₁ ⊢ τ : κ₂
    κ₂ layout
    ---------------------- (ForAll)
    Σ ⊢ ∀ α : κ₁ -> τ : κ₂

    Σ ⊢ τ : κ₁
    κ₁ <: κ₂
    ----------- (Sub)
    Σ ⊢ τ : κ₂

## Typing rules for terms

    ------------------------- (Var)
    Σ; Γ, x_ϕ : τ ⊢ x_ϕ :_ϕ τ

     Σ; Γ ⊢ e :_s τ
    ---------------- (Lift)
    Σ; Γ ⊢ ⌈e⌉ :_d τ

    Σ ⊢ τ₁ : κ      Σ; Γ, x_ϕ : τ₁ ⊢ e :_s τ₂
    ----------------------------------------- (Lam-S)
    Σ; Γ ⊢ fun (x_ϕ : τ₁) -> e :_s τ₁ ->_ϕ τ₂

    Σ; Γ, x_ϕ : τ₁ ⊢ e :_d τ₂   Σ ⊢ τ₁ concrete
    ------------------------------------------- (Lam-D)
     Σ; Γ ⊢ fun (x_ϕ : τ₁) -> e :_d τ₁ ->_ϕ τ₂

    Σ; Γ ⊢ f :_s τ₁ ->_s τ₂   Σ; Γ ⊢ e :_s τ₁
    ----------------------------------------- (App-S-S)
                Σ; Γ ⊢ f e :_s τ₂

    Σ; Γ ⊢ f :_d τ₁ ->_d τ₂   Σ; Γ ⊢ e :_d τ₁   Σ ⊢ τ₁ concrete
    ------------------------------------------------------------ (App-D-D)
                         Σ; Γ ⊢ f e :_d τ₂

    Σ; Γ ⊢ f :_s τ₁ ->_d τ₂   Σ; Γ ⊢ e :_d τ₁
    ----------------------------------------- (Spec)
              Σ; Γ ⊢ f · e :_d τ₂

    Σ; Γ ⊢ f :_d τ₁ ->_s τ₂   Σ; Γ ⊢ e :_s τ₁
    ----------------------------------------- (App-D-S)
              Σ; Γ ⊢ f e :_d τ₂

       Σ, α : κ; Γ ⊢ e :_ϕ τ   α ∉ fv(Γ)
    ---------------------------------------- (TyLam)
    Σ; Γ ⊢ Fun (α : κ) -> e :_ϕ ∀ α : κ -> τ

    Σ; Γ ⊢ f :_ϕ ∀ (α : κ) -> τ   Σ ⊢ σ : κ
    --------------------------------------- (TyApp)
            Σ; Γ ⊢ f[σ] :_ϕ τ{σ/α}

## The static computation operator `⌊-⌋`

The important theorem we want is:

  **Theorem 1.** If `· ⊢ e : τ` then `· ⊢ ⌊e⌋ : τ`.

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
