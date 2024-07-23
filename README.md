# DepFix: Dependent Fixpoints!

Positive (but not strictly!) iso-recursive types implemented in Agda with `postulate`s and `rewrite` rules. My main motivation with exploring this is to see if these ideas might work for the core theory of my own language (i.e. as an alternative to W-types/containers/descriptions). Take a look at the [Examples](./src/Examples)!

- Positive Inductive Types: [Simple.agda](./src/Simple.agda)
  - Examples: [Nat.agda](./src/Examples/Nat.agda)
- Inductive-Recursive Types: [IndRec.agda](./src/IndRec.agda)
  - Examples: [Universe.agda](./src/Examples/Universe.agda), 
  [FreshList.agda](./FreshList.agda)
- Indexed Types: [Indexed.agda](./src/Indexed.agda)
  - Examples: [Vector.agda](./src/Examples/Vector.agda)
- Inductive-Inductive Types: [IndexedIndRec.agda](./src/IndexedIndRec.agda) 
  - Examples: [TTInTT.agda](./src/Examples/TTinTT.agda)

If anyone knows of any papers/other resources exploring similar approaches to adding recursive types in dependent type systems please let me know; I've really struggled to find anything! I am very excited about how this technique, with just small extensions, can readily support quite complex inductive definitions involving induction-recursion and induction-induction.
