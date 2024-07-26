# DepFix: Dependent Fixpoints!

Positive (but not strictly!) iso-recursive types implemented in Agda with `postulate`s and `rewrite` rules. My main motivation with exploring this is to see if these ideas might work for the core theory of my own language (i.e. as an alternative to W-types/containers/descriptions). Take a look at the [Examples](./src/Examples)!

- Positive Inductive Types: [Simple.agda](./src/Simple.agda)
  - Examples: [Nat.agda](./src/Examples/Nat.agda)
- Inductive-Recursive Types: [IndRec.agda](./src/IndRec.agda)
  - Examples: [Universe.agda](./src/Examples/Universe.agda), [FreshList.agda](.//src/Examples/FreshList.agda)
- Indexed Types: [Indexed.agda](./src/Indexed.agda)
  - Examples: [Vector.agda](./src/Examples/Vector.agda), [Forest.agda](./src/Examples/Forest.agda)
- Inductive-Inductive Types: [IndexedIndRec.agda](./src/IndexedIndRec.agda) 
  - Examples: [TTinTTSimple.agda](./src/Examples/TTinTTSimple.agda), [TTinTT.agda](./src/Examples/TTinTT.agda)

## Remaining Questions

- Can we encode *truly nested* types (like bushes)?
- Can large elimination be obtained *without* `Setω`?
  - I think parameterising `Functor` over the universe `Level` we will eliminate into (lifting it out from the signatures of `All`/`all`) would be a good starting point. However, this makes giving reasonable signatures for `replace`/`fmap` and the laws (which rely on taking the outputs from eliminating and collecting them back into the `Functor` structure) a challenge.

## Related Work

I haven't been able to find any treatment in the literature of encoding inductive definitions exactly like my approach here (which I shall henceforth refer to as `DepFix`), but I am aware of a couple similar-ish approaches (which are also interesting to compare against in general, to get a sense for the extent of the design-space).
- Cedille's encoding of inductive datatypes as fixpoints of functors ([Generic Derivation of Induction for Impredicative Encodings in Cedille](https://homepage.divms.uiowa.edu/~astump/papers/cpp-2018.pdf))
  - The core difference between that work and `DepFix` is that I do not try to derive induction (for which Cedille relies on their dependent intersection) but instead ask for enough extra operations in the `Functor` typeclass as to give an appropriate signature and beta-rule for a postulated induction principle.  
  - Another difference is that Cedille's implementation of functor fixpoints relies on impredicativity (specifically, when applying `FixC` to `AlgC`), while I just postulate the existence of fixpoints.
- Universes of descriptions ([Descriptions](https://effectfully.blogspot.com/2016/04/descriptions.html))
  - `DepFix` can be viewed as the very starting-point in implementing a universe of datatype descriptions: I have specified the operations I would like to have defined over all in-univese types and laws I would like to hold, but refrained from actually choosing any specific set of type codes/implementing said operations up-front. 
  - A neat trick which one can play with descriptions is that they themselves are just datatypes and so, with care, one can describe a universe of descriptions in terms of itself (see [The Gentle Art of Levitation](https://personal.cis.strath.ac.uk/conor.mcbride/levitation.pdf)). In comparison, "levitation" for `DepFix` (inside a theory which already supports and exposes the `Functor` encoding and `Fix`/`fix` primitives) is trivial.

    Specifically, all we need is a datatype like
    ```agda
    data MyFix (F : Set → Set) ⦃ _ : Functor F ⦄ : Set where
      fix : F (Fix F) → Fix F
    ```
    and the functor-encoding of this (obtained in the usual way - by replacing every recursive occurence of `MyFix F` with parameter `A`) is simply

    ```agda
    MyFixD : (F : Set → Set) → ⦃ Functor F ⦄ → Set → Set
    MyFixD F A = F A

    MyFix : (F : Set → Set) → ⦃ Functor F ⦄ → Set
    MyFix F = Fix (MyFixD F)
    --      = Fix F
    ```
    I will leave it to the reader to form an opinion on whether this is interesting, or obvious.
  - A significant disadvantage of `DepFix` vs descriptions is that we have less control over the set of inductive datatypes one can later define (e.g. I don't know of a way to ensure strict positivity). For this reason, and some more subtle technical ones regarding how Agda does its positivity and termination checking (see the explanation at the bottom of [Simple.agda](./src/Simple.agda)) we cannot hope to implement `DepFix` in `--safe` Agda.

If anyone knows of any papers/other resources exploring similar techniques, please let me know! I'm honestly quite surprised this inductive-datatypes-directly-as-fixpoints-of-functors approach isn't more common.
