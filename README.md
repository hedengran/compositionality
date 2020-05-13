# Compositionality Theory in HOL4

This repository contains two formalizations of a compositionality theory for the theorem prover [HOL4](https://hol-theorem-prover.org).

## Shortkeys for unicode symbols

For this theory a number of unicode symbols have been defined for readability.

| Term | Infix symbol | Infix style | Emacs Shortcut | 
|------|--------------|-------------|----------------|
| Refines | ⊑ | Non-associative | C-S-M-q q |
| And | ⊓ | Non-associative | C-S-M-q i |
| Composition | ₓ | Left-associative| C-M-_ x | 
| Implements | ◁ | Non-associative | C-M-\| , |

## Acknowledgements

This formalization uses a Contract Theory syntax, and semantic interpretation, based on [[1]](#1).

## References
<a id="1">[1]</a> 
Nyberg, M., Westman, J., & Gurov, D. (2019). 
Proving Compositionality in a Non-Monotonic Contracts-Theory.
Unpublished work.
