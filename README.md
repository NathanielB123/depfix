# DepFix: Dependent Fixpoints!

Positive (but not strictly!) iso-recursive types implemented in Agda with `postulate`s and `rewrite` rules. My main motivation with exploring this is to see if these ideas might work for the core theory of my own language (i.e. as an alternative to W-types/containers/descriptions). Take a look at the [Examples](./src/Examples)!

- Positive Inductive Types: [Simple.agda](./src/Simple.agda)
  - Examples: [Nat.agda](./src/Examples/Nat.agda), [Forest.agda](./src/Examples/Forest.agda)
- Inductive-Recursive Types: [IndRec.agda](./src/IndRec.agda)
  - Examples: [Universe.agda](./src/Examples/Universe.agda), [FreshList.agda](.//src/Examples/FreshList.agda)
- Indexed Types: [Indexed.agda](./src/Indexed.agda)
  - Examples: [Vector.agda](./src/Examples/Vector.agda)
- Inductive-Inductive Types: [IndexedIndRec.agda](./src/IndexedIndRec.agda) 
  - Examples: [TTinTT.agda](./src/Examples/TTinTT.agda)

## Remaining Questions

- Can we encode *truly nested* types (like bushes)?
- Can we get large elimination *without* `Setω`?
  - I think parameterising `Functor` over the universe `Level` we will eliminate into (lifting it out from the signatures of `All`/`all`) would be a good starting point. However, this makes giving reasonable signatures for `replace`/`fmap` and the laws (which rely on taking the outputs from eliminating and collecting them back into the `Functor` structure) a challenge.
- Can we write stronger versions of the `Functor` laws, which cover the dependent cases?
- So far, I have investigated very little meta-theory behind the encoding I showcase here (henceforth referred to as `DepFix`) but I think there is evidence to believe that `DepFix` (or something similar) can be integrated into existing predicative (it is well-known that non-strictly positive types are unsound when combined with impredicativity - [Positivity, strict and otherwise](https://counterexamples.org/strict-positivity.html)) type systems while preserving important properties like normalisation, soundness and canonicity. Below, I sketch a couple (partial) proofs of canonicity and normalisation (very informally - a real proof would likely have to take the logical relations/NbE route, or prove equivalence with some other datatype encoding which we know satisfies these properties). If you think I have made any significant mistakes in my arguments, please tell me (i.e. file a GitHub issue)!
  - **Canonicity:** The only new non-canonical constant introduced by `DepFix` (at least in the [Simple](./src/Simple.agda) implementation) is `Fix-elim`, which blocks on the "scrutinee" definitionally equalling `fix x` for some `x`. Therefore, canonicity hinges on all elements of `Fix F` (the type of said "scrutinee") reducing to `fix x` in an empty context. There are two new constants/typing rules (depending on your perspective) which can produce `Fix F`s: `fix` and `Fix-elim`. By induction on lists of partial terms headed by `Fix-elim` (with holes for the scrutinee), canonicity reduces to proving that `Fix-elim` terminates.
  - **Normalisation:** I argue `DepFix` preserves strong normalisation (even in false contexts) because `Fix-elim` only recursively calls itself via `all`. To take the fixpoint of a non-well-founded inductive type (from which a loop could in theory be derived), one could define an `all` which directly relies on the false assumption, (in which case, it will get stuck) or one could implement a type-correct `All`/`all` for which the `Functor` laws do not hold (in which case, I believe that `Fix-elim`s will always reach a least fixpoint - e.g. examples of such type-correct-but-wrong `All`/`all` implementations are ones where `All` ignores its arguments and returns `⊤` in every case. I am actually not sure how to prove this though!)

## Related Work

I haven't been able to find any treatment of encoding inductive definitions exactly like `DepFix` in the literature, but I am aware of a couple similar-ish approaches (which are also interesting to compare against in general, to get a sense for the extent of the design-space).
- Cedille's encoding of inductive datatypes as fixpoints of functors ([Generic Derivation of Induction for Impredicative Encodings in Cedille](https://homepage.divms.uiowa.edu/~astump/papers/cpp-2018.pdf))
  - The core difference between that work and `DepFix` is that I do not try to derive induction (for which Cedille relies on their dependent intersection) but instead ask for enough extra operations in the `Functor` typeclass as to give an appropriate signature and beta-rule for a postulated induction principle.  
  - Another difference is that Cedille's implementation of least fixpoints relies on impredicativity (specifically, when applying `FixC` to `AlgC`), while I just postulate the existence of fixpoints.
- Universes of descriptions ([Descriptions](https://effectfully.blogspot.com/2016/04/descriptions.html))
  - `DepFix` can be viewed as the very starting-point in implementing a universe of datatype descriptions: I have specified the operations I would like to have defined over all in-univese types and laws I would like to hold, but refrained from actually choosing any specific set of type codes/implementing said operations up-front. 
  - A neat trick which one can play with descriptions is that they themselves are just datatypes and so, with care, one can describe a universe of descriptions in terms of itself (see [The Gentle Art of Levitation](https://personal.cis.strath.ac.uk/conor.mcbride/levitation.pdf)). In comparison, "levitation" for `DepFix` (inside a theory which already supports and exposes the `Functor` encoding and `Fix`/`fix` primitives) is trivial.

    Specifically, all we need is a datatype like
    ```agda
    data MyFix (F : Set → Set) ⦃ _ : Functor F ⦄ : Set where
      fix : F (MyFix F) → MyFix F
    ```
    and the functor-encoding of this (obtained in the usual way - by replacing every recursive occurence of `MyFix F` with parameter `MyFixR`) is simply

    ```agda
    MyFixD : (F : Set → Set) → ⦃ Functor F ⦄ → Set → Set
    MyFixD F MyFixR = F MyFixR

    MyFix : (F : Set → Set) → ⦃ Functor F ⦄ → Set
    MyFix F = Fix (MyFixD F)
    --      = Fix F
    ```
    I will leave it to the reader to form an opinion on whether this is interesting, or obvious.
  - A significant disadvantage of `DepFix` vs descriptions is that we have less control over the set of inductive datatypes one can later define (e.g. I don't know of a way to ensure strict positivity). For this reason, and some more subtle technical ones regarding how Agda does its positivity and termination checking (see the explanation at the bottom of [Simple.agda](./src/Simple.agda)) we cannot hope to implement `DepFix` in `--safe` Agda.

If anyone knows of any papers/other resources exploring similar techniques, please let me know! I'm honestly quite surprised this inductive-datatypes-directly-as-fixpoints-of-functors approach isn't more common.
