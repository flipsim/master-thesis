# Free Deduction as Sessions

This repository contains the mechanized formalization of the process calculus
$\pi FD$ which accompanies the thesis, written in the [Rocq Prover](https://rocq-prover.org/). The main results of the thesis are collected in `Results.v`.

For a mapping between the human-readable lemmata in the thesis and their identifiers
in this codebase, please refer to the Mechanization Map in the appendix of the thesis.

## Dependencies
To build this development, you need the **Rocq Prover** and the **Equations** plugin.
The easiest way to install these dependencies is via [opam](https://opam.ocaml.org/doc/Install.html).

### Requirements
* **Rocq** (v9.1.1 or later recommended)
* **Equations** plugin

### Installation via opam
If you have `opam` installed, you can install the required dependencies by running:

```bash
opam repo add rocq-released https://rocq-prover.org/opam/released
opam update
opam install rocq-prover=9.1.1 rocq-equations
```

### Building the Project
To compile the development, simply run `make` in the `formalization` directory.

## Project Structure
We give a short summary of the most important parts of the formalization.

### 1. Syntax & Variable Binding
* **Syntax.v**: Contains the definition of the abstract syntax of processes, messages, and statements, formalized using de Bruijn indices. The file additionally contains:
  - A mutual induction principle for processes.
  - A function computing the depth of a process, for proofs that follow by induction on the depth.
  - Substitution of messages for variables in processes.
* **Substitution.v**: Contains properties about substitutions, such as the _substitution lemma_.
* **FreeVars.v**: Collects useful properties about free variables.

### 2. Types and Typing
* **Types.v**: Syntax of the language types.
* **Contexts.v**: Formalization of linear typing contexts and context splitting.
* **Typing.v**: Contains the rules of the typing relation.

### 3. Operational Semantics
* **StructCong.v**: Definition of structural congruence, proof of type preservation under structural congruence and depth-indexed relation for proofs by induction on derivation depth.
* **Reduction.v**: Definitions of contraction and reduction. Also includes a depth-indexed variant of contraction.

### 4. Canonical Forms and Termination
* **FinalProcess.v**: Definition of _canonical cut forms_ and _final processes_,
along with properties about their reducibility.
* **Irreducibility.v**: Contains the proof that final processes are irreducible.

### 5. Metatheory (Type Safety & Church-Rosser)
* **Preservation.v**: Proof of type preservation.
* **Progress.v**: Proof of progress (deadlock freedom).
* **Confluence.v**: Contains the proofs of the Church-Rosser property. Auxiliary results
and definitions are distributed across multiple files:
  - **AxCutCtx.v**, containing the definition of evaluation contexts and axcut reducts.
  - **ParallelReduction.v**, containing the definition of _simple reduction_ and _parallel reduction_.
  - **DirectedCong.v**, containing the definition of _directed congruence_.
  - **EquivRedProperties.v**, containing properties about simple reduction.
