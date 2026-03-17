# Artifact for PLDI 2026 Paper #701: Responsive Parallelism with Dynamic and First-class Priorities

This artifact consists of the source code for the PriML compiler, extended with implementations of the paper's theory of dynamic and first-class priorities. The artifact also includes the benchmarks described in the paper and experiment scripts for running the compiler on them.

**Note:** The claims made in the paper about the benchmarks cover only their compilation, and not properties about their execution. Therefore, the push-button evaluation for this artifact will only compile the benchmarks and not run them. We provide instructions for separately compiling and running (some of) the benchmarks, but note that the Docker container is not set up out of the box for, e.g., testing parallel scaling of the benchmarks, or running the web server benchmark.

## What to Download

If you're looking at this README file on, e.g., Zenodo, and trying to figure out what you need to download to run the artifact, there are two options:

1. Download everything. This is the preferred, maximally compatible, option for evaluating the artifact. You can optionally rebuild the artifact following the instructions under "Building and Navigating the Artifact" below.
2. Download everything *except* the pre-built Docker image, `priml-dfc-artifact.tar`. Skip any `docker load` commands. This requires downloading less up-front, but will require an internet connection to download additional material while building the artifact, and is therefore discouraged for the PLDI artifact evaluation process but may be preferable to anyone reusing this artifact later.

## Hardware and Software Requirements

The only requirement for successful evaluation of this artifact is the ability to build and run Docker containers. We developed and tested the artifact on Ubuntu 24.04 with 32 GB of memory and 512 GB of disk.

It is possible to evaluate the artifact outside of the Docker container on Unix systems by installing the dependencies listed under "Building and Navigating the Docker Image" (on Ubuntu, you can run the `RUN` commands listed in the `Dockerfile`), but we do not provide detailed instructions for doing so.

## Quick Start: Push-button Evaluation

This evaluation loads the pre-built Docker image and performs the experiments to reproduce Table 2 of the paper, which summarizes the results of Section 4.3: Quantitative Evaluation.

Navigate to the top level of the artifact (the folder containing `Dockerfile`) and run the below (possibly using `sudo` if necessary):

    docker load -i priml-dfc-artifact.tar
    ./run_paper.sh

The first command loads the Docker container and may take a minute. The second command should take seconds and will output, in CSV format, the raw data for Table 2, giving the number of priority constraints generated, and time for Hindley-Milner type inference, constraint generation, constraint solving, and overall compilation.

An example output on our test system is:

    benchmark, constraints,HM,gen,solve,total
    deadline,45,231,137,1822,0m0.029s
    exhaust-sync,735,206,458,56180,0m0.097s
    nqueens-serv,508,579,1880,56571,0m0.099s
    web,631,1304,3500,120245,0m0.195s

Note that columns HM, gen, and solve are in microseconds, so you should divide by 1000 to get the corresponding number in Table 2. Column total is given in minutes and seconds, so you should multiply the number of seconds by 1000 to get the corresponding number in Table 2. Exact time values will differ due to hardware differences and Docker overheads. The number of constraints (column constraints) should match the above sample output exactly.

## Components and Directory Structure

The artifact includes the following files subfolders:

    domainslib - The source code for Priodomainslib[20], used for running tasks in the OCaml backend
    priml - The source code for the extended PriML compiler
    priml-examples
      web-extended - the Web Server benchmark
      dfc_examples - other benchmarks
        regression - regression tests (including some not using dynamic/first-class priorities)
    scripts - experiment scripts
    sml-lib - Tom Murphy VII's Standard ML libraries, used in the PriML compiler
    build.sh - script to build the Docker container
    Dockerfile - used for building the Docker image to evaluate the artifact
    Makefile - for building the PriML compiler
    README.md - this file
    run_paper.sh - script to run the paper evaluation in the Docker container
    run_regression.sh - script to run the regression suite in the Docker container
    start.sh - script to start the Docker container for interactive evaluation
    
Note that `domainslib`, PriML, and `sml-lib` are distributed under their own licenses; see the respective COPYING, LICENSE, and/or README files for more details.

## Claims of the paper

Here, we summarize the artifact-related claims made in the paper with pointers to appropriate sections of the paper and to sections of this document that describe how to evaluate the claims.

* Section 4.1. Type Inference: We have extended PriML's type inference to handle dynamic and first-class priorities. We describe the modified source files below under "Navigating the Source Code". This claim is also evaluated by compiling the benchmark files, throughout the push-button and detailed evaluation.
* Section 4.2. Compilation to OCaml: We have developed a new backend for PriML that compiles typechecked PriML programs to Multicore OCaml. We describe the modified source files below under "Navigating the Source Code". This claim is also evaluated by compiling the benchmark files, because compilation automatically invokes the OCaml backend and the OCaml compiler in order to produce executables.
* Section 4.3. Quantitative Evaluation: We test the compiler using 4 benchmark programs and report run times for several components of the compilation pipeline as well as overall compilation time and the number of constraints generated. See "Components and Directory Structure" above for the locations of the benchmarks within the artifact and "Push-button evaluation" above for how to reproduce the results of this subsection.
* Section 5. Case Study: We built a small but working web server, based on a benchmark in earlier versions of PriML, using the new language features described in this paper. The code structure is described below in "Navigating the Web Server Case Study", and the case study is compiled along with the other benchmarks when reproducing the quantitative evaluation, as described in the previous bullet point.

## Detailed Evaluation
### Building and Navigating the Docker Image

If desired, you can rebuild the Docker container.
**Note:** Building the artifact requires an internet connection and will download existing images. If you don't have an internet connection in your setup or don't want to download new items during the test, skip to "You could instead load..."
In the top level of the artifact (the folder containing `Dockerfile`), run

    ./build.sh
    
to build the Docker image containing artifact. This extends an Ubuntu 24.04 image with the following dependencies necessary for building and running the artifact:

* Standard GNU utilities: `wget`, `make`, `time`
* GCC
* `libgmp-dev` (the GNU Multiple Precision arithmetic library, needed for MLton)
* The OPAM package manager for OCaml, with OCaml 5.2.0 and `ocamlfind` (for compiling PriML programs using the OCaml backend)
* [MLton](http://mlton.org/)

It also builds the PriML compiler. Instructions for rebuilding it manually are below. The entire build process will likely take several minutes.


You could instead load the pre-built container using

    docker load -i priml-dfc-artifact.tar

You can then start the container interactively using

    ./start.sh

This will open a shell in the top level directory of the artifact, which mirrors the directory structure of the artifact described above in "Components and Directory Structure" except that the scripts in `scripts/` are moved to the top level inside the Docker container, and `domainslib/` is moved one level up, to the `ubuntu` home directory on the container.

### Navigating the Source Code (Optional; Supports Claims in Sections 4.1 and 4.2)

The modifications to PriML to support dynamic and first-class priorities are primarily in the following files (all under `priml/`):

* `el.sml` - In the ASTs for the "external language", unify priority literals and variables, and allow expressions where priorities are expected.
* `parser/parse.sml` - In the parser, no longer require hardcoded priority literals as parameters to `spawn` and other commands.
* `elab/elaborate.sml` - Perform Hindley-Milner type inference. This file was extended to type expressions of priority type.
* `elab/psetcstrs.sml` - New file. Define priority constraints and operations over them as described in Section 4.1.1.
* `constraint.sml` - New file. Constraint generation from a typed AST as described in Section 4.1.2.
* `solve.sml` - New file. Constraint solving as described in Section 4.1.3
* `solverctx.sml` - New file. A primitive solver that uses the priority relationships in the context to determine whether priority constraints are satisfied.
* `depriocaml.sml` - New file (based on the previous Standard ML backend). Compile PriML-specific features to calls to the Priodomainslib library for Multicore OCaml, as described in Section 4.2
* `printcaml.sml`, `compilecaml.sml` - New files that output and compile OCaml code from an AST output by `depriocaml`.

### Rebuilding the PriML Compiler (Optional; Supports Claims in Sections 4.1 and 4.2)

The PriML compiler is already built in the process of building the Docker container. If you wish to rebuild it, start the Docker container as described above in "Building and Navigating the Docker Image" and run

    cd priml
    make

This should take under a minute (producing a number of compiler warnings) and produces an executable `primlc` in the top level of the artifact (`/home/ubuntu/Priml-DFC` in the Docker container).

### Navigating the Benchmarks (Optional; Supports Claims in Sections 4.3)

The source files containing the four benchmarks described in Section 4.3 can be found as follows:

* "deadline": `priml-examples/dfc_examples/deadline4.prm`
* "exhaust-sync": `priml-examples/dfc_examples/regression/exhaust_sync.prm`
* "nqueens-serv": `priml-examples/dfc_examples/nqueensserv.prm`
* "web": `priml-examples/web-extended` (described in more detail below)

### Reproducing the Quantitative Evaluation (Supports Claims in Sections 4.3)

In an interactive session in the Docker container, you can run the experiments to recreate the data in Table 2 (other than the LoC column, which requires inspection of the source code), by running (at the top level of the artifact, `/home/ubuntu/Priml-DFC`):

    ./paper.sh

This is equivalent to running `./run_paper.sh` outside the Docker container and produces the same output, as described above in "Quick Start: Push-button Evaluation"

### Compiling and running individual benchmarks (Optional)

Here, we describe how to compile individual PriML source files if desired, assuming you are in an interactive session in the Docker container. The PriML compiler is invoked as follows:

    /path/to/primlc <benchmark>.prm <output_executable> [ocaml_files]

The last argument is an optional list of OCaml source files to be compiled and linked with the output of the PriML compiler. This is only necessary for the web server benchmark. The command above will compile the .prm file using the PriML compiler, compile it to OCaml, and invoke the OCaml compiler to produce an executable. It will also output various statistics about compilation (all times are in microseconds):

* Init time: Time to produce the initial context for the solver.
* WF time: Time to solve well-formedness constraints.
* Imp time: Time to solve implication constraints.
* LE time: Time to solve boundedness constraints.
* Parse and Desugar Time: Time spent in the parser.
* HM: Time for Hindley-Milner type inference.
* gen: Time for constraint generation.
* solve: Time for constraint solving.
* constraints: Number of priority constraints generated.
* Number solver calls: Calls to an external solver (deprecated, will always report 0 because an external solver is not used in this version of the code)
* Total time in solver: Total time used by `solverctx.sml` to determine constraint satisfaction.
* OCaml Generation Time: Time to compile away PriML-specific features and output OCaml source code.
* OCaml Compilation Time: Total time to invoke the OCaml compiler on the generated OCaml source.

In our experiments to produce Table 2, the "total" column is end-to-end running time of `primlc`, determined by prepending `time` to the command above.

You can run the generated executable using

    eval $(opam env)
    ./<output_executable>

This runs the executable on 9 system threads (the number of threads is currently hardcoded). The first command sets the environment variables needed for the OCaml runtime.

Most of the benchmarks produce no output, with a notable exception being "nqueens-serv", which will repeatedly prompt the user for a number greater than 0 and will compute the number of solutions to the N-Queens problem for the N given by the user. The computation will be done in the background with the result reported when it completes, and the user can enter more numbers in the meantime. "Small" requests (defined as N<12) are computed at a higher priority than larger requests. Entering "done" terminates the prompt loop, waits for any outstanding computations to terminate, and then exits.

### Navigating the Web Server Case Study (Optional; Supports Claims in Section 5)

The code for the web server case study is contained in `priml-examples/web-extended`, which contains the following files:

    lib.ml - OCaml wrappers around hash table and network libraries
    Makefile
    time.ml - OCaml wrappers around time functions
    web.prm - PriML source code for the case study

All of the code excerpts listed in Section 5 of the paper came from `web.prm`, which contains all of the PriML source code. You can build the web server case study by running `make` in the folder above (assuming you are in an interactive session in the Docker container).

Note that the artifact is not designed for testing the case study, but running it opens a server on port 8000 serving the page `priml-examples/www/index.html`.

### Running Regression Tests (Optional)

The artifact contains a suite of small tests in `priml-examples/dfc_examples/regression`. You can run this suite in two ways:

* In the Docker container, in `/home/ubuntu/Priml-DFC`: `./regression.sh`
* Outside the container but after having built it, in the top level folder of the artifact: `./run_regression.sh`

In either case, the output should be a series of rows of the following form:

    test_name result time

where `result` is 0, indicating successful compilation, or 1, indicating compilation error.

**Important:** Tests prefixed with `bad` intentionally contain priority inversions or other PriML type errors and therefore should have a result of 1. 

The last column is the compilation time in seconds. As these are very small tests, all compile in less than 0.1 seconds on our test machine.
