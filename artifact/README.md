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

### Option 2: Installing on a native Debian/Ubuntu

You can follow the instructions in INSTALL.md to setup DynamiTe on a Debian/Ubuntu machine. The instructions have been tested on a *Ubuntu 18.04* system and a *Debian GNU/Linux 10 (buster)* system.

## Usage

1. To run DynamiTe on an example

    ```
    python3 dynamo.py [options] <example.c>
    ```

2. Command-line options

- `--term`, `-t`: proving termination only (by the `ProveT` algorithm)
- `--nonterm`, `-nt`: proving non-termination only (by the `ProveNT` algorithm)
- Without `--term` or `--nonterm`: enable the integrated algorithm `ProveTNT`, which automatically chooses either `ProveT` and `ProveNT` and switches to the other if failed.
- `--dfs`, `-dfs`: use depth-first-search, instead of breath-first-search, in `ProveNT`
- `--all_rcs`, `-all-rcs`: find and return all recurrent sets, instead of the first valid recurrent set 

3. Output

- Termination algorithm: `Termination result: True` if the program terminates.
- Non-termination algorithm: `Non-termination result: False` with recurrent sets if the program does not terminate.
- The integrated algorithm: `TNT result:` `True` if the program terminates, `False` with the non-terminating loop's position and a recurrent set if the program does not terminate.
- Statistics
    - `infer_ranking_functions`: total time to infer ranking functions
    - `validate_ranking_functions`: total time to validate ranking functions
    - `strengthen`: total time to learn new recurrent sets
    - `verify`: total time to validate recurrent sets
    - `prove`: total proving time

# Step-by-Step Instructions

## Benchmarks

The folder `dynamite/benchmarks` contains 4 benchmarks:
- `termination-crafted-lit`: terminating linear programs in the SV-COMP's `termination-crafted-lit` benchmark used in Figure 6.
- `nontermination-crafted-lit`: non-terminating linear programs in the SV-COMP's `termination-crafted-lit` benchmark used in Figure 7.
- `nla-term`: terminating non-linear programs used in Figure 8.
- `nla-nonterm`: non-terminating non-linear programs used in Figure 9.
- Both `nla-term` and `nla-nonterm` are used in Figure 10.

## Reproducing the Results

To reproduce the results in Figures 6, 7, 8, 9, and 10, in the folder `dynamite/benchmarks`, run `make BENCH_NAME` where `BENCH_NAME` is the name of the corresponding benchmark to a figure, `integrated` for Figure 10. The following results were collected from runs on a Docker image. The default timeout is **300s** for each benchmark program. The result tables in HTML will be automatically generated, which can be viewed from the command line using `lynx`. The details are as follows:

- To reproduce Figure 6, run
    ```
    make termination-crafted-lit
    ```
    It took about 75 minutes to run the entire 61 benchmark programs 5 times. The result can be found [here](https://htmlpreview.github.io/?https://github.com/letonchanh/dynamite/blob/master/artifact/results/termination-crafted-lit/termination-crafted-lit.out-udP0tHK.html), whose log files are in the folder [results/termination-crafted-lit/out-udP0tHK](results/termination-crafted-lit/out-udP0tHK). Some inferred ranking functions that can be verified in Figure 6 now cannot be verified before the timeout due to the resource limitation of the Docker container.
    
- To reproduce Figure 7, run
    ```
    make nontermination-crafted-lit
    ```
    It took about 30 minutes for 5 runs. The result can be found [here](https://htmlpreview.github.io/?https://github.com/letonchanh/dynamite/blob/master/artifact/results/nontermination-crafted-lit/nontermination-crafted-lit.out-1xdwZWJ.html) (log files in [results/nontermination-crafted-lit/out-1xdwZWJ](results/nontermination-crafted-lit/out-1xdwZWJ)). We cannot handle the non-deterministic program `ChenCookFuhsNimkarOHearn-TACAS2014-Introduction.c`. The result of this example was wrongly reported in Figure 7 due to a bug in the symbolic execution.
    
- To reproduce Figure 8, run
    ```
    make nla-term
    ```
    It took about 150 minutes to run the entire 38 benchmark programs. The result can be found [here](https://htmlpreview.github.io/?https://github.com/letonchanh/dynamite/blob/master/artifact/results/nla-term/nla-term.out-ZL8GkEB.html) (log files in [results/nla-term/out-ZL8GkEB](results/nla-term/out-ZL8GkEB)). Note that the learned ranking functions from some examples (e.g `bresenham1`, `cohencu1`) that can be verified in Figure 8 now cannot be verified before the timeout due to the resource limitation of the Docker container.
    
- To reproduce Figure 9, run
    ```
    make nla-nonterm
    ```
    It took about 60 minutes to run the entire 39 benchmark programs. The result can be found [here](https://htmlpreview.github.io/?https://github.com/letonchanh/dynamite/blob/master/artifact/results/nla-nonterm/nla-nonterm.out-G0n3q9k.html) (log files in [results/nla-nonterm/out-G0n3q9k](results/nla-nonterm/out-_8ejxcU)). The result is better than the result reported in Figure 9, thank to an improvement in the symbolic execution. The improved symbolic execution can capture more precise transition relations of loops, that helps to successfully validate more candidate recurrent sets.
    
- To reproduce Figure 10, which is the result of running the integrated algorithm `ProveTNT` on the two benchmarks `nla-term` and `nla-nonterm`, run
    ```
    make integrated
    ```
    It took about 200 minutes to run the entire 2 benchmarks. The two results are available at [`nla-term`](https://htmlpreview.github.io/?https://github.com/letonchanh/dynamite/blob/master/artifact/results/integrated/nla-term.integrated-6rEMxHR.html) ([log files](results/integrated/integrated-6rEMxHR)) and [`nla-nonterm`](https://htmlpreview.github.io/?https://github.com/letonchanh/dynamite/blob/master/artifact/results/integrated/nla-nonterm.integrated-TfpfczU.html) ([log files](results/integrated/integrated-TfpfczU)).
    
- Run
    ```
    make all
    ```
    for all the above experiments.

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
