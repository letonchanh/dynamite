# Overview

DynamiTe is an analysis system for searching termination and non-termination proofs of imperative non-linear programs. The system combines *dynamic* strategies for discovering invariants and sampling transitive closure with *static* refinement into an overall framework for proving termination or nontermination of those programs. For termination, the tool infers ranking functions from concrete transitive closures, and, for non-termination, the tool iteratively collects executions and dynamically learns conditions to refine recurrent sets. These two strategies can mutually inform each other, taking counterexamples from a failed validation in one endeavor and crossing both the static/dynamic and termination/non-termination lines, to create new execution samples for the other one.

# Getting Started

The DynamiTe project is open source and hosted at https://github.com/letonchanh/dynamite. The artifact for the paper "DynamiTe: Dynamic Termination and Non-termination Proofs" is available to download at ???.

## Setup instructions

We provide two different ways to setup and run DynamiTe. For the kick-the-tires phase, we recommend the easiest **Option 1 (Using Docker)** for you to quickly setup the tool and try it on some simple examples. Because DynamiTe takes advantage of multicore systems (e.g., our evaluation in the paper uses a 20-core machine), we suggest **Option 2 (Installing on native Debian/Ubuntu)** to fully reproduce our results.

### Option 1: Using Docker

The following steps show how to build DynamiTe's Docker image via the provided Dockerfile and run it

0. Install Docker

    Follow the instructions on https://docs.docker.com/install/. You may need to run `docker` commands with `sudo` or similar privileges.

1. Build the DynamiTe's Docker image
    ```
    docker build -t dynamite .
    ```
    The image is built on top of the pre-built base image [`letonchanh/dynamite:base`](https://hub.docker.com/r/letonchanh/dynamite) on Docker Hub. The base image contains all dependencies to run DynamiTe and it can also be built offline with the following command
    ```
    docker build -f Dockerfile.base -t dynamite_base .
    ```
    
2. Run the Docker image
    ```
    docker run -it dynamite bash
    ```

### Option 2: Installing on native Debian/Ubuntu

You can follow the instructions in INSTALL.md to setup DynamiTe on a Debian/Ubuntu machine. The instructions have been tested on a *Ubuntu 18.04* system and a *Debian GNU/Linux 10 (buster)* system.

## Basic testing of the artifact

# Step-by-Step Instructions

## Benchmarks

The folder `dynamite/benchmarks` contains 4 benchmarks:
- `termination-crafted-lit`: terminating linear programs in the SV-COMP's `termination-crafted-lit` benchmark, which was used in Figure 6.
- `nontermination-crafted-lit`: non-terminating linear programs in the SV-COMP's `termination-crafted-lit` benchmark, which was used in Figure 7.
- `nla-term`: terminating non-linear programs used in Figure 8.
- `nla-nonterm`: non-terminating non-linear programs used in Figure 9.

## Reproducing the Results

To reproduce the results in Figures 6, 7, 8, and 9, in the folder `dynamite/benchmarks`, run `make BENCH_NAME` where `BENCH_NAME` is the name of the corresponding benchmark to a figure. The default timeout is **300s** for each benchmark program. The details are as follows:

- To reproduce Figure 6, run
    ```
    make termination-crafted-lit
    ```
    It took about ??? minutes for DynamiTe to run the whole benchmark on the Docker image.
    
- To reproduce Figure 8, run
    ```
    make nla-term
    ```
    It took about 150 minutes for DynamiTe to run the entire 38 benchmarks on the Docker image. The result can be found [here](https://htmlpreview.github.io/?https://github.com/letonchanh/dynamite/blob/master/artifact/results/nla-term/nla-term.out-ZL8GkEB.html), whose log files are in the folder [results/nla-term/out-ZL8GkEB](results/nla-term/out-ZL8GkEB). Note that the learned ranking functions of some examples (e.g `bresenham1`, `cohencu1`) that can be verified in Figure 8 now cannot be verified before the timeout due to the limited resources in the Docker image.
    
- To reproduce Figure 9, run
    ```
    make nla-nonterm
    ```
    It took about 60 minutes for DynamiTe to run the entire 39 benchmarks on the Docker image. The result can be found [here](https://htmlpreview.github.io/?https://github.com/letonchanh/dynamite/blob/master/artifact/results/nla-nonterm/nla-nonterm.out-G0n3q9k.html), whose log files are in the folder [results/nla-nonterm/out-G0n3q9k](results/nla-nonterm/out-_8ejxcU). The result is better than the result reported in Figure 9, thank to an improvement in the symbolic execution. The improved symbolic execution can capture more precise transition relations of the loops, that helps to successfully validate more candidate recurrent sets.

- How to reproduce any experiments or other activities that support the conclusions in the paper.

- If the artifact runs for more than a few minutes, point this out, note how long it is expected to run (roughly) and explain how to run it on smaller inputs.

- Descriptions of and links to files (included in the archive) that represent expected outputs (e.g., the log files expected to be generated by your tool on the given inputs); if there are warnings that are safe to be ignored, explain which ones they are.

- A list of claims from the paper supported by the artifact, and how/why.

- A list of claims from the paper not supported by the artifact, and why not. (Dynamite takes advantage of multicore systems (e.g., our evaluation uses a 20-core machine))

## Browsing the Code

DynamiTe was mainly developed in Python 3, but its program instrumentation was implemented in OCaml with [CIL](https://github.com/cil-project/cil). 

- `src/`: The main source folder of DynamiTe.
    - `dynamo.py`: The main driver of DynamiTe.
    - `analysis.py`: The main algorithms of DynamiTe.
        - `class Setup`: Pre-processing of the analysis, such as executing the programs to collect snapshots and loop information (loop conditions, stems, and lassos), setting up external tools (e.g the dynamic inference tool DIG) and SMT solvers (e.g z3, CVC4).
        - `class Term`: Implementation of the termination algorithm in Figure 2, whose the main method `prove` aims to prove termination of every loop in the program. Below is the list of auxiliary procedures and their corresponding names (in round brackets) in Figure 2.
            - `prove_term_vloop`: Proving termination of a loop in the program (`ProveT`).
            - `infer_ranking_functions`: Inferring a list of ranking functions from collected snapshots (`InferRF`).
            - `validate_ranking_functions`: Validating the inferred ranking functions (`ValidateRFs`).
        - `class NonTerm`: Implementation of the non-termination algorithm in Figure 3, whose the main method `prove` aims to prove non-termination of a loop in the program.
            - `prove_nonterm_vloop`: Searching for a valid recurrent set for proving non-termination of a loop in the program (`ProveNT`).
            - `verify`: Checking if a candidate recurrent set is valid.
            - `strengthen`: Refining an invalid recurrent set by strengthening it with new inferred constraints (`RefineRS`). The method `DynInfer` for dynamically inferring invariants from snapshots in Figure 3 was implemented as the interface `dig.infer_from_traces` to the DIG tool.
        - `class TNT`: Implementation of the integrated algorithm in Figure 5.
    - `validate.py`: Wrappers of the external validators such as CPAchecker, Ultimate Automizer, Ultimate Taipan and their portfolio (to run them in parallel).
    - `solver.py`: Wrappers of the external SMT solvers.
    - `parsers.py`: Parsers of the external tools' output.
    - `lib.py`: Utilities for snapshots, including collecting and classifying them, or inferring invariants from them.
    - `utils/`: Other utilities, such as timing, setting values.
- `deps/`: Dependencies of DynamiTe
    - `dig/`: The [DIG](https://github.com/unsat/dig) tool for dynamically inferring program invariants.
    - `dynamite-instr`: The DynamiTe's transformations, which are implemented as CIL extensions.
        - `src/cil/src/ext/transform`: The program transformation to collect dynamic snapshots.
        - `src/cil/src/ext/validate`: The program instrumentation to validate the list of ranking functions of a loop.
