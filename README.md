# DepFix: Dependent Fixpoints!

Positive (but not strictly!) iso-recursive types implemented in Agda with `postulate`s and `rewrite` rules. My main motivation with exploring this is to see if these ideas might work for the core theory of my own language (i.e. as an alternative to W-types).

- Positive Inductive Types: [Simple.agda](./src/Simple.agda)
- Inductive-Recursive Types: [IndRec.agda](./src/IndRec.agda)
- Inductive-Inductive Types: WIP
- Indexed Types: WIP

If anyone knows of any papers/other resources exploring similar approaches to adding recursive types in dependent type systems please let me know; I've really struggled to find anything!
