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

The type constructs are type atoms, arrow types, n-ary products, n-ary sums, and continuations. Acknowledging that the presence of continuation effects in expressions means that evaluation order matters, we specify a lazy call-by-value dynamics. The semantics and normalization are now complicated by the fact that effects are not separated, requiring us to weave the continuation monad everywhere.
