Taglierino: A symbolic protocol verifier
========================================

Taglierino is a domain-specific language for specifying and verifying
cryptographic protocols in Haskell.  Protocols are written in a format similar
to process calculi used in other verification tools
(e.g. [ProVerif](https://prosecco.gforge.inria.fr/personal/bblanche/proverif/)).
Taglierino compiles down these descriptions to finite automata that can be
analyzed by the [LTSA model
checker](https://www.doc.ic.ac.uk/~jnm/LTSdocumention/LTSA.html).

