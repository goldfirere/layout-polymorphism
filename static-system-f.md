# System F with representation polymorphism

This is meant to be an *internal* language, produced via an elaboration
step from surface OCaml.

    x ::= ...               Term variables
    α ::= ...               Type variables
    ξ ::= ...               Kind variables
    ϕ ::=                   Obligations
      | [n; ξs]             Number of bound variables; set of free variables
    b ::=                   Base values
      | ...                 Integers, constructors, etc.
    B ::= ...               Base types
    e, f ::=                Terms
      | x                   Variable with phase
      | fun (x :_ϕ τ) -> e  Term abstraction
      | e e                 Normal application
      | Fun (α : κ) -> e    Type abstraction
      | e[τ]                Type application
      | FUN (ξ <: κ) -> e   Kind abstraction
      | e{κ}                Kind application
      | ⌈e⌉                 Specialize
      | b                   Base values
    v ::=                   Values
      | fun (x :_ϕ τ) -> e  Term abstraction
      | Fun (α : κ) -> v    Type abstraction over value
      | FUN (ξ <: κ) -> v   Kind abstraction over value
      | b                   Base values
    τ, σ ::=                Types
      | α                   Type variable
      | τ ->_ϕ τ            Function
      | ∀ (α : κ) -> τ      Polymorphic function
      | ∀ (ξ <: κ) -> τ     Kind-polymorphic function
      | B                   Base types
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
    θ ::=                   Substitutions
      | ∅                   Empty
      | θ ∘ κ/ξ             Kind substitution
      | θ ∘ τ/α             Type substitution
      | θ ∘ e/x             Term substitution

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

    Δ ⊢ κ rep ::=

    Δ ⊢ κ rep
    ------------------ (Var)
    Δ, ξ <: κ rep

    -------------- (Concrete)
    Δ ⊢ C rep

This unary relation, `rep`, checks whether a layout has enough information
to actually be compiled (i.e. it is representable).
Notably, `Δ ⊢ any rep` does *not* hold.

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

## Base types

    B : C ::= ...

## Typing rules for types

    Δ; Σ ⊢ τ : κ ::=

    ------------------- (TyVar)
    Δ; Σ, α : κ ⊢ α : κ

    B : C
    ------------ (Base)
    Δ; Σ ⊢ B : C

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

## Obligation assumption

    Δ; ϕ ⊢ κ rep =def
      assuming (∀ ξ s.t. ξ ∈ snd ϕ: Δ ⊢ ξ rep), then Δ ⊢ κ rep

This more general than we really need, because
kinds here are so simple. So we can simplify this to

    Δ; ϕ ⊢ κ rep =def
      (Δ ⊢ κ rep) ∨ (κ ∈ snd ϕ)

which is more clearly decidable.

## Base values

    b : B ::= ...

## Typing rules for terms

    Δ; Σ; Γ ⊢ e :_ϕ τ ::=

    ------------------------------ (Var)
    Δ; Σ; Γ, x :_ϕ τ ⊢ x :_ϕ τ

    b : B
    --------------- (Base)
    Δ; Σ; Γ ⊢ b : B

    Δ, ξ₁ <: κ₁', ⋯, ξⱼ <: κⱼ'; Σ; Γ ⊢ e :_(ϕ, ξ₁, ⋯, ξⱼ) τ
    θ₀ = ∅
    ∀ i s.t. 1 ≤ i ≤ j:
      fv(κᵢ') ⊆ (dom(Δ) ∪ {ξ₁, ⋯, ξᵢ₋₁})
      θᵢ = κᵢ/ξᵢ ∘ θᵢ₋₁
      Δ ⊢ κᵢ <: κᵢ'{θᵢ₋₁}
      Δ ⊢ κᵢ rep
    --------------------------------------------------------------------- (Spec)
    Δ; Σ; Γ ⊢ ⌈(FUN (ξ₁ <: κ₁') ⋯ (ξⱼ <: κⱼ') -> e){κ₁}{⋯}{κⱼ}⌉ :_ϕ τ{θⱼ}

    Δ; Σ; Γ ⊢ e :_ϕ τ
    ----------------------- (Sub)
    Δ; Σ; Γ ⊢ e :_(ϕ, ϕ') τ

    Δ; Σ ⊢ τ₁ : κ
    Δ ⊢ κ layout
    Δ; ϕ ⊢ κ rep
    Δ; Σ; Γ, x :_ϕ τ₁ ⊢ e :_s τ₂
    ---------------------------------------------- (Lam)
    Δ; Σ; Γ ⊢ fun (x :_ϕ' τ₁) -> e :_ϕ τ₁ ->_ϕ' τ₂

    Δ; Σ; Γ ⊢ f :_ϕ τ₁ ->_s τ₂
    Δ; Σ; Γ ⊢ e :_ϕ τ₁
    Δ; Σ ⊢ τ₁ : κ₁
    Δ; ϕ ⊢ κ₁ rep
    ----------------------------------------- (App)
    Δ; Σ; Γ ⊢ f e :_ϕ τ₂

    fv(κ) ⊆ dom(Δ)
    Δ; Σ, α : κ; Γ ⊢ e :_ϕ τ
    --------------------------------------------- (TyLam)
    Δ; Σ; Γ ⊢ Fun (α : κ) -> e :_ϕ ∀ (α : κ) -> τ

    Δ; Σ; Γ ⊢ f :_ϕ ∀ (α : κ) -> τ₂
    Δ; Σ ⊢ τ₁ : κ
    ----------------------------------------------- (TyApp)
    Δ; Σ; Γ ⊢ f[τ₁] :_ϕ τ₂{τ₁/α}

    fv(κ) ⊆ dom(Δ)
    Δ, ξ <: κ; Σ; Γ ⊢ e :_ϕ τ
    --------------------------------------------- (KiLam)
    Δ; Σ; Γ ⊢ FUN (ξ <: κ) -> e :_ϕ ∀ (ξ <: κ) -> τ

    Δ; Σ; Γ ⊢ e :_ϕ ∀ (ξ <: κ₂) -> τ
    Δ ⊢ κ <: κ₂
    ------------------------------ (KiApp)
    Δ; Σ; Γ ⊢ e{κ} :_ϕ τ{κ/ξ}

## Operational semantics

    Δ; Σ ⊢ e₁ ⟶ e₂ ::=

    ---------------- (Spec)
    Δ; Σ ⊢ ⌈e⌉ ⟶ e

    Δ; Σ ⊢ τ : κ
    Δ ⊢ κ rep   (* this is the key check! *)
    ------------------------------------------- (Beta)
    Δ; Σ ⊢ (fun (x :_ϕ τ) -> e₁) v₂ ⟶ e₁{v₂/x}

    Δ; Σ ⊢ e₁ ⟶ e₁'
    ----------------------- (App1)
    Δ; Σ ⊢ e₁ e₂ ⟶ e₁' e₂

    Δ; Σ ⊢ e₂ ⟶ e₂'
    ----------------------- (App2)
    Δ; Σ ⊢ v₁ e₂ ⟶ v₁ e₂'

    Δ; Σ, α : κ ⊢ e ⟶ e'
    --------------------------------------------- (TyAbs)
    Δ; Σ ⊢ Fun (α : κ) -> e ⟶ Fun (α : κ) -> e'

    --------------------------------------- (TyBeta)
    Δ; Σ ⊢ (Fun (α : κ) -> v)[τ] ⟶ v{τ/α}

    Δ; Σ ⊢ e ⟶ e'
    --------------------- (TyApp)
    Δ; Σ ⊢ e[τ] ⟶ e'[τ]

    Δ, ξ <: κ; Σ ⊢ e ⟶ e'
    ----------------------------------------------- (KiAbs)
    Δ; Σ ⊢ FUN (ξ <: κ) -> e ⟶ FUN (ξ <: κ) -> e'

    ------------------------------------------- (KiBeta)
    Δ; Σ ⊢ (FUN (ξ <: κ₁) -> v){κ₂} ⟶ v{κ₂/ξ}

    Δ; Σ ⊢ e ⟶ e'
    --------------------- (KiApp)
    Δ; Σ ⊢ e{κ} ⟶ e'{κ}

## Type safety

### Theorem (Preservation). (thm:pres)

If Δ; Σ; Γ ⊢ e :_ϕ τ and Δ; Σ ⊢ e ⟶ e', then Δ; Σ; Γ ⊢ e' :_ϕ τ.

#### Proof

By induction on the reduction relation.

Case (Spec).

    Δ; Σ ⊢ ⌈e⌉ ⟶ e                                            Given
    Typing rule (Spec) applies      		                only possibility
    e = FUN (ξ₁ <: κ₁') ⋯ (ξⱼ <: κⱼ') -> e'){κ₁}{⋯}{κⱼ}         Conclusion of (Spec)
    Δ, ξ₁ <: κ₁', ⋯, ξⱼ <: κⱼ'; Σ; Γ ⊢ e' :_(ϕ, ξ₁, ⋯, ξⱼ) τ₀   Premise of (Spec)
    θ₀ = ∅                                                      Premise of (Spec)
    ∀ i s.t. 1 ≤ i ≤ j:
      θᵢ = κᵢ/ξᵢ ∘ θᵢ₋₁
      Δ ⊢ κᵢ <: κᵢ'{θᵢ₋₁}
      Δ ⊢ κᵢ rep
    τ = τ₀{θⱼ}                                                  Conclusion of (Spec)
    Δ; Σ; Γ ⊢ e :_(ϕ, ξ₁, ⋯, ξⱼ) τ                              Straightforward use of typing rules
