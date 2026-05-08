# Simply Typed

An intrinsically-typed development of simple type systems with type-driven implementations of denotational semantics and normalization-by-evaluation.

## Blueprint

### • STLC (✓ [DSL.STLC](https://github.com/LiamSchilling/simply-typed/blob/master/src/DSL/STLC.agda))

The type constructs are type atoms and arrow types. Normalization is [typical](https://en.wikipedia.org/wiki/Normalisation_by_evaluation).

### • STLC with product and sum types

The type constructs are type atoms, arrow types, n-ary products, and n-ary sums. Normalization now requires the nondeterminism monad in the style of [Altenkirch and Uustalu (2004)](https://people.cs.nott.ac.uk/psztxa/publ/Nbe2.pdf).

### • STLC with continuations and a model separation of effects

The type constructs are type atoms, arrow types, n-ary products, n-ary sums, continuations, and suspended commands. The semantics and normalization now require the [continuation monad](https://ncatlab.org/nlab/show/continuation+monad).

### • STLC with continuations

The type constructs are type atoms, arrow types, n-ary products, n-ary sums, and continuations. Acknowledging that the presence of continuation effects in expressions means that evaluation order matters, we specify a lazy call-by-value dynamics. The semantics and normalization are now complicated by the fact that effects are not separated, requiring us to weave the continuation monad throughout.

## References

- Abel, Andreas. Normalization by evaluation: Dependent types and impredicativity. Habilitation. Ludwig-Maximilians-Universität München (2013) https://www.cse.chalmers.se/~abela/talkHabil2013.pdf.
- Olivier Danvy, Chantal Keller, and Matthias Puech. Typeful Normalization by Evaluation. In 20th International Conference on Types for Proofs and Programs (TYPES 2014). Leibniz International Proceedings in Informatics (LIPIcs), Volume 39, pp. 72-88, Schloss Dagstuhl – Leibniz-Zentrum für Informatik (2015) https://doi.org/10.4230/LIPIcs.TYPES.2014.72.
- Paweł Wieczorek and Dariusz Biernacki. 2018. A Coq formalization of normalization by evaluation for Martin-Löf type theory. In Proceedings of the 7th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2018). Association for Computing Machinery, New York, NY, USA, 266–279. https://doi.org/10.1145/3167091
