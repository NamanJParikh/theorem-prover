# A Theorem Prover
This project contains a theorem prover for classical propositional logic written functionally in OCaml.

## Usage
Build the project using ```opam exec -- dune build``` and run using ```opam exec -- dune exec prover```

The program will search for a proof of the inputted propositional formula in classical logic and return ```true``` if the formula is a tautology and ```false``` otherwise. Be aware that only capital letters are accepted by the parser for atomic propositions.

## The Logic Type and Parsing
This logic uses the connectives Not, And, Or, Implies, True, False. In particular, biimplication is not implemented. The precedence order of connectives in the parser is Implies, Or, And, then Not.

## Soundness and Completeness for Classical Propositional Logic
This program uses a modified implication left rule that is less flexible than Gentzen's rule in the LK Sequent Calculus. Because of this, the logic here may not be complete in the derivability of all valid sequents. However, it is still complete in the derivability of all valid propositions given empty antecedents. Soundness of all sequents, however, holds.

## Inversions
This theorem prover is not currently optimized to handle invertible inference rules prior to conducting synchronous search. Inversions or an adaptation of linear logic may be added in the future.

## Acknowledgements
The basic structure of this code, particularly the logic module, are based on the logic module provided in 15-317 (Constructive Logic) at CMU for the purposes of writing a theorem prover for constructive propositional logic.
