# System F with representation polymorphism

This is meant to be an *internal* language, produced via an elaboration
step from surface OCaml.

    x ::= ...               Term variables
    α ::= ...               Type variables
    ξ ::= ...               Kind variables
    i, j, n ::=             Natural numbers
      | 0                   Zero
      | S(n)                Non-zero
    ϕ ::=                   Obligations
      | ξs                  Set of free kind variables
    b ::=                   Base values
      | ...                 Integers, constructors, etc.
    B ::= ...               Base types
    e, f ::=                Terms
      | x                   Variable
      | fun (x :_ϕ τ) -> e  Term abstraction
      | e e                 Normal application
      | Fun (α : κ) -> e    Type abstraction
      | e[τ]                Type application
      | FUN (ξ <: κ) => e   Templated kind abstraction
      | e{κ}                Templated kind application
      | let x = e in e      Local variable
      | ⌈e⌉                 Specialize
      | b                   Base values
    v ::=                   Values
      | fun (x :_ϕ τ) -> e  Term abstraction
      | Fun (α : κ) -> v    Type abstraction over value
      | FUN (ξ <: κ) => v   Templated kind abstraction over value
      | b                   Base values
    τ ::=                   Types
      | α                   Type variable
      | τ ->_ϕ τ            Function
      | ∀ (α : κ) -> τ      Polymorphic function
      | B                   Base types
    σ ::=                   Type schemes
      | τ                   Non-templated type
      | ∀ (ξ <: κ) => σ     Templated kind polymorphism
    K ::=                   Base kinds
      | any                 Top kind
      | R                   Representable base kind
    R ::=                   Representable base kinds
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
      | Γ, x :_ϕ σ          Variable
    θ ::=                   Substitutions
      | ∅                   Empty
      | θ ∘ κ/ξ             Kind substitution
      | θ ∘ τ/α             Type substitution
      | θ ∘ e/x             Term substitution

All contexts should be viewed as sets and allow arbitrary well-scoped
permutation. We follow the Barendregt convention throughout, meaning
that all new local variables are assumed to be distinct from variables
already in scope; these freshness constraints are omitted from the rules
and can easily be enforced by renaming.

## Well-formed kinds

    Δ ⊢ κ ok ::=

    fv(κ) ⊆ dom(Δ)
    -------------- (Scoped)
    Δ ⊢ κ ok

Any well-scoped kind is considered well-formed.

## Kind contexts

    ⊢ Δ ok ::=

    ------------- (Empty)
    ⊢ ∅ ok

    ⊢ Δ ok
    Δ ⊢ κ ok
    -------------- (KVar)
    ⊢ Δ, ξ <: κ

## Typing rules for kinds

    Δ ⊢ κ layout ::=

    Δ ⊢ κ layout
    -------------------- (Var)
    Δ, ξ <: κ ⊢ ξ layout

    ⊢ Δ ok
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
    Δ, ξ <: κ ⊢ ξ rep

    ⊢ Δ ok
    -------------- (Base)
    Δ ⊢ R rep

This unary relation, `rep`, checks whether a layout has enough information
to actually be compiled (i.e. it is representable).
Notably, `Δ ⊢ any rep` does *not* hold.

## Subtyping for kinds

There is a subtype relation on kinds.

    Δ ⊢ κ₁ <: κ₂ ::=

    ⊢ Δ, ξ <: κ ok
    ------------------ (Var)
    Δ, ξ <: κ ⊢ ξ <: κ

    ⊢ Δ ok
    Δ ⊢ κ ok
    -------------- (Any)
    Δ ⊢ κ <: any

    ⊢ Δ ok
    Δ ⊢ κ ok
    -------------- (Refl)
    Δ ⊢ κ <: κ

    Δ ⊢ κ₁ <: κ₂
    Δ ⊢ κ₂ <: κ₃
    ------------ (Trans)
    Δ ⊢ κ₁ <: κ₃

## Type contexts

    Δ ⊢ Σ ok ::=

    ⊢ Δ ok
    -------- (Empty)
    Δ ⊢ ∅ ok

    Δ ⊢ Σ ok
    Δ ⊢ κ ok
    --------------- (TyVar)
    Δ ⊢ Σ, α : κ ok

## Base types

    B : C ::= ...

## Typing rules for types

    Δ; Σ ⊢ τ : κ ::=

    Δ ⊢ Σ, α : κ ok
    ------------------- (TyVar)
    Δ; Σ, α : κ ⊢ α : κ

    B : C
    Δ ⊢ Σ ok
    ------------ (Base)
    Δ; Σ ⊢ B : C

    Δ; Σ ⊢ τ₁ : κ₁
    Δ ⊢ κ₁ layout
    Δ; Σ ⊢ τ₂ : κ₂
    Δ ⊢ κ₂ layout
    ------------------------------ (Arrow)
    Δ; Σ ⊢ τ₁ ->_ϕ τ₂ : value

    Δ ⊢ κ₁ ok
    Δ; Σ, α : κ₁ ⊢ τ : κ₂
    Δ ⊢ κ₂ layout
    -------------------------- (ForAll)
    Δ; Σ ⊢ ∀ (α : κ₁) -> τ : κ₂

    Δ; Σ ⊢ τ : κ₁
    Δ ⊢ κ₁ <: κ₂
    ------------- (Sub)
    Δ; Σ ⊢ τ : κ₂

## Typing rules for type schemes

    Δ; Σ ⊢ˢ σ : κ ::=

    Δ; Σ ⊢ τ : κ
    ------------- (Regular)
    Δ; Σ ⊢ˢ τ : κ

    Δ, ξ <: κ₀; Σ ⊢ˢ σ : κ
    Δ ⊢ κ layout
    ------------------------------ (KForAll)
    Δ; Σ ⊢ˢ FUN (ξ <: κ₀) => σ : κ

## Obligation assumption

    Δ; ϕ ⊢ κ rep =def
      assuming (∀ ξ s.t. ξ ∈ snd ϕ: Δ ⊢ ξ rep), then Δ ⊢ κ rep

This more general than we really need, because
kinds here are so simple. So we can simplify this to

    Δ; ϕ ⊢ κ rep =def
      (Δ ⊢ κ rep) ∨ (κ ∈ snd ϕ)

which is more clearly decidable.

## Term contexts

    Δ; Σ ⊢ Γ ok ::=

    Δ ⊢ Σ ok
    ----------- (Empty)
    Δ; Σ ⊢ ∅ ok

    Δ; Σ ⊢ˢ σ : κ
    Δ; ϕ ⊢ κ rep
    Δ; Σ ⊢ Γ ok
    ϕ ⊆ dom(Δ)
    -------------------------- (TermVar)
    Δ; Σ ⊢ Γ, x :_ϕ σ ok

## Base values

    b : B ::= ...

## Typing rules for terms

    Δ; Σ; Γ ⊢ e :_ϕ σ ::=

    Δ; Σ ⊢ Γ, x :_ϕ σ ok
    ------------------------------ (Var)
    Δ; Σ; Γ, x :_ϕ σ ⊢ x :_ϕ σ

    b : B
    Δ; Σ ⊢ Γ ok
    --------------- (Base)
    Δ; Σ; Γ ⊢ b :_??? B

    Δ; Σ ⊢ τ₁ : κ
    Δ ⊢ κ layout
    Δ; ϕ ⊢ κ rep
    Δ; Σ; Γ, x :_ϕ' τ₁ ⊢ e :_??? τ₂
    ---------------------------------------------- (Lam)
    Δ; Σ; Γ ⊢ fun (x :_ϕ' τ₁) -> e :_ϕ τ₁ ->_ϕ' τ₂

    Δ; Σ; Γ ⊢ f :_ϕ τ₁ ->_ϕ' τ₂
    Δ; Σ; Γ ⊢ e :_ϕ' τ₁
    Δ; Σ ⊢ τ₁ : κ₁
    Δ; ϕ ⊢ κ₁ rep
    ??? ϕ ϕ'
    ----------------------------------------- (App)
    Δ; Σ; Γ ⊢ f e :_??? τ₂

    Δ ⊢ κ ok
    Δ; Σ, α : κ; Γ ⊢ e :_ϕ τ
    --------------------------------------------- (TyLam)
    Δ; Σ; Γ ⊢ Fun (α : κ) -> e :_ϕ ∀ (α : κ) -> τ

    Δ; Σ; Γ ⊢ f :_ϕ ∀ (α : κ) -> τ₂
    Δ; Σ ⊢ τ₁ : κ
    ----------------------------------------------- (TyApp)
    Δ; Σ; Γ ⊢ f[τ₁] :_ϕ τ₂{τ₁/α}

    Δ ⊢ κ ok
    Δ, ξ <: κ; Σ; Γ ⊢ e :_ϕ σ
    --------------------------------------------- (KiLam)
    Δ; Σ; Γ ⊢ FUN (ξ <: κ) -> e :_ϕ ∀ (ξ <: κ) -> σ

    Δ; Σ; Γ ⊢ e :_ϕ ∀ (ξ <: κ₂) -> τ
    Δ ⊢ κ <: κ₂
    ------------------------------ (KiApp)
    Δ; Σ; Γ ⊢ e{κ} :_ϕ τ{κ/ξ}

    Δ; Σ; Γ ⊢ e₁ :_ϕ' σ₁
    Δ; Σ; Γ, x :_ϕ' σ₁ ⊢ e₂ :_ϕ τ₂
    ???? ϕ ϕ'
    --------------------------------- (Let)
    Δ; Σ; Γ ⊢ let x = e₁ in e₂ :_ϕ τ₂

## Operational semantics

    Δ; Σ ⊢ e₁ ⟶ e₂ ::=

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

## Basic properties

### Lemma (Regularity). (lem:reg)

1. If `⊢ Δ ok`, then `fv(Δ) = ∅`.
1. If `Δ ⊢ κ layout`, then `⊢ Δ ok` and `fv(κ) ⊆ dom(Δ)`.
1. If `Δ ⊢ κ rep`, then `Δ ⊢ κ layout`.
1. If `Δ ⊢ κ₁ <: κ₂`, then `⊢ Δ ok`, `fv(κ₁) ⊆ dom(Δ)`, and `fv(κ₂) ⊆ dom(Δ)`.
1. If `Δ ⊢ Σ ok`, then `⊢ Δ ok` and `fv(Σ) = ∅`.
1. If `Δ; Σ ⊢ τ : κ`, then `Δ ⊢ Σ ok`, `fv(τ) ⊆ (dom(Δ) ∪ dom(Σ))`, and `fv(κ) ⊆ dom(Δ)`.
1. If `Δ; Σ ⊢ Γ ok`, then `Δ ⊢ Σ ok` and `fv(Γ) = ∅`.
1. If `Δ; Σ; Γ ⊢ e :_[n; ξs] τ`, then `Δ; Σ ⊢ Γ ok`, `fv(e) ⊆ (dom(Δ) ∪ dom(Σ) ∪ dom(Γ))`,
    `Δ; Σ ⊢ τ : κ`, `Δ ⊢ κ layout`, `τ is headed by n kind quantification`, and `ξs ⊆ dom(Δ)`.

## Type safety

### Theorem (Preservation). (thm:pres)

If Δ; Σ; Γ ⊢ e :_ϕ τ and Δ; Σ ⊢ e ⟶ e', then Δ; Σ; Γ ⊢ e' :_ϕ τ.

#### Proof

By induction on the reduction relation.

Case (Spec).

    Δ; Σ ⊢ ⌈e⌉ ⟶ e                                            Given
    Let ϕ = [n; ξs].                                            only possibility
    Typing rule (Spec) applies, possibly after some (Sub)s      only possibility
    Let ϕ' = [n; ξs'], where ξs' ⊆ ξs                           premise of (Sub)
    e = e'{κ₁}{⋯}{κⱼ}                                           Conclusion of (Spec)
    Δ; Σ; Γ ⊢ e' :_[n + j; ξs') ∀ (ξ₁ <: κ₁') ⋯ (ξⱼ <: κⱼ') -> τ₀   Premise of (Spec)
    θ₀ = ∅                                                      Premise of (Spec)
    ∀ i s.t. 1 ≤ i ≤ j:
      θᵢ = κᵢ/ξᵢ ∘ θᵢ₋₁
      Δ ⊢ κᵢ <: κᵢ'{θᵢ₋₁}
      Δ ⊢ κᵢ rep
    τ = τ₀{θⱼ}                                                  Conclusion of (Spec)
    WTP: Δ; Σ; Γ ⊢ e'{κ₁}{⋯}{κⱼ} :_[n; ξs] τ                    Substitution
    WTP: Δ; Σ; Γ ⊢ e'{κ₁}{⋯}{κⱼ} :_[n; ξs'] τ                   (Sub)

## Compilation

Let `⌊e⌋ = ⌊e⌋_∅`.

Define `⌊e⌋_θ` recursively by the following functions:

    ⌊e{κ₁}{⋯}{κⱼ}⌋_θ = ⌊e₀{θ'}⌋_θ    (j ≥ 1 and is chosen maximally)
      where e{θ} = FUN (ξ₁ <: κ₁') ⋯ (ξⱼ <: κⱼ') => e₀
            θ' = {κ₁/ξ₁}{⋯}{κⱼ/ξⱼ}

    ⌊let x = e₁ in e₂⌋_θ = let x = ⌊e₁⌋_θ in ⌊e₂⌋_(θ ∘ e₁/x)

    other forms homomorphically

Define `⌊Γ⌋` to be `Γ` but without any bindings where the type is a
non-`τ` `σ`-type.

Define `Σ; Γ ⊩ e : τ` to be like `Δ; Σ; Γ ⊢ e : σ`, but without rules
(KiLam) and (KiApp). In addition, treat `Δ` and `ϕ` as empty everywhere.

Then:

Theorem (Compilation is possible). If `∅; Σ; Γ ⊢ e :_∅ τ`, then `Σ; ⌊Γ⌋ ⊩ ⌊e⌋ : τ`.
Theorem (Compilation is possible). If `Δ; Σ; Γ ⊢ e :_ϕ τ`, then for any ρs, `Σ{ρs/Δ}; ⌊Γ⌋{ρs/Δ} ⊩ ⌊e⌋ : τ{ρs/Δ}
RAE: Next step is actually to write out the no-kind-variables language. This "it's just like the other
one except where it's not" doesn't really cut it.

Proof.

By induction on the typing derivation.

Case Var: Easy.
Case Base: Easy.
Case Lam: Assumptions:

    ∅; Σ ⊢ τ₁ : κ
    ∅ ⊢ κ layout
    ∅; ∅ ⊢ κ rep
    ∅; Σ; Γ, x :_ϕ' τ₁ ⊢ e :_??? τ₂
    ------------------------------
    ∅; Σ; Γ ⊢ fun (x :_ϕ' τ₁) -> e :_∅ τ₁ ->_∅ τ₂

Must prove that κ is not a variable nor `any`. Follows from
∅; ∅ ⊢ κ rep.

Case KiLam:

    ∅ ⊢ κ ok
    ∅, ξ <: κ; Σ; Γ ⊢ e :_ϕ σ
    --------------------------------------------- (KiLam)
    ∅; Σ; Γ ⊢ FUN (ξ <: κ) -> e :_ϕ ∀ (ξ <: κ) -> σ



Theorem (Compilation is correct). If Δ; Σ ⊢ e ⟶* e', then ∅; Σ ⊢ ⌊e⌋ ⟶* ⌊e'⌋

# Talk outline

Setting:
  - unboxed types, including #{ ... } syntax
  - arrays interface
  - we need layout flexibility
  - red herring: we don't need full layout polymorphism, because we don't
    generally use the same layout variable twice.
Challenge: we can't compile layout flexibility efficiently
  (we can pretty easily do it inefficiently!)
Solution: specialization.
  - but this means we have to have the function body around during compilation
  - even though we need to continue to support separate compilation.
  - this isn't so bad, actually: we just notate in a cmi file that the actual function can be found
    somewhere else (specifically: cmx files) (PS: this is not planned for the bytecode compiler, where
    there will be no unboxing)
Challenge: we need to know in advance that inlining is even possible
Solution: prenex polymorphism, which must be instantiated immediately (with concrete layouts) at usage sites
  - this is interesting: our source language has no polymorphism, just subtyping. But we need
    polymorphism to track this feature in an intermediate language.
  - how do we know this is right? We can compile the intermediate language to the L language
    of the levity-polymorphism paper.
Challenge: modules
Solution: prenex polymorphism.
  - that is, a module is just a runtime structure. Like other runtime structures, it must
    have any layout polymorphism in prenex position -- **at top level**.
  - usage sites will have to specialize the modules, but this can be transparent to the user.
  - We'll also allow for abstract layouts in module types that can be specialized with `with` --
    that's no problem and is largely orthogonal to the rest of this.
Seems easy in retrospect, but we've been thinking about this problem for a while and it only
came to me when making this presentation!

If time: demo actual features that exist:
  - include functor
  - local
  - comprehensions
  - immutable arrays
