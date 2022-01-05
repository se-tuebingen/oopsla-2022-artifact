# Artifact for the OOPSLA 2022 paper 'Effects, Capabilities, and Boxes'

This github repository constitutes the artifact for our paper

> Effects, Capabilities, and Boxes: From Scope-based Reasoning to Type-based Reasoning and Back.
> Jonathan Immanuel Brachthäuser, Philipp Schuster, Edward Lee, Aleksander Boruch-Gruszecki.
> Conditionally accepteed at OOPSLA 2022.

The artifact consists of two parts:

1. Coq proofs, proving soundness of the calculus System C
2. A website featuring an implementation of System C with examples that can be typechecked, edited, and run.

## Getting Started
While the repository contains the sources of the website, we do not propose to
build the website yourself. Instead, we use github-pages to host the artifact,
which is available at

  <https://se-tuebingen.github.io/oopsla-2022-artifact/>

The website contains

- [Documentation of the proofs](https://se-tuebingen.github.io/oopsla-2022-artifact/proofs/), with [detailed information](https://se-tuebingen.github.io/oopsla-2022-artifact/proofs/Top.SystemC.Definitions.html) on how the Coq mechanization corresponds to the calculus as it is presented in the paper.

- [An executable implementation](https://se-tuebingen.github.io/oopsla-2022-artifact/tutorial/) of the calculus.

We claim reusability of the proofs and the interactive demo, but not of the calculus _implementation_ itself.

### Kick-the-tires: Demo Website
For the kick-the-tires phase, please perform the following steps, which should not require more than 1 minute:

1. Visit the prepared [artifact website](https://se-tuebingen.github.io/oopsla-2022-artifact/).
   It is hosted on github and will not reveal any information to us.

   (If you want to be sure, you can use a proxy and check the `network` tab in the developer tools. It should only load files from the same website and should not make any additional connections).

   The compiler for System C is compiled to JavaScript and runs in the browser, so please allow scripts to be executed.

2. Visit the [tutorial page](https://se-tuebingen.github.io/oopsla-2022-artifact/tutorial/#repls)
   and click the `run` button on the right. The compiler will be loaded, the example above will
   be executed and it should output `"Hello World!\n()"`.


### Kick-the-tires: Coq Proofs
We believe it is not strictly necessary to compile the Coq proofs yourself. Instead,
we have set up continuation integration (github action) to compile the proofs.

To check validity of the proofs, you may visit the [github action](https://github.com/se-tuebingen/oopsla-2022-artifact/actions/workflows/proof-ci.yml) page that contains successful compilation runs of Coq.

For the CI run that corresponds to this release, please visit:

<https://github.com/se-tuebingen/oopsla-2022-artifact/runs/4701644774?check_suite_focus=true#step:4:379>

TODO WE NEED TO UPDATE THE LINK

<details>
To manually navigate to this run, you may select the `build` job and expand `Run coq-community/docker-coq-action@v1`, and finally expand `Build`. You should see the output of `coqc`, which
should look like

```
- COQDEP VFILES
  - COQC Taktiks.v
  - COQC FSetNotin.v
  - COQC ListFacts.v
  - COQC FSetDecide.v
  - COQC AdditionalTactics.v
  - COQC FiniteSets.v
  - COQC Atom.v
  - COQC Label.v
  - File "./Label.v", line 112, characters 0-56:
  Warning: - Warning: Declaring a scope implicitly is deprecated; use in advance an
  - explicit "Declare Scope metatheory_scope.". [undeclared-scope,deprecated]
  - File "./Atom.v", line 269, characters 0-77:
  Warning: - Warning: Declaring a scope implicitly is deprecated; use in advance an
  - explicit "Declare Scope metatheory_scope.". [undeclared-scope,deprecated]
  - COQC Environment.v
  - COQC Signatures.v
  - COQC Metatheory.v
  - COQC Nat.v
  - COQC CaptureSets.v
  - COQC Rho_Definitions.v
  - COQC Rho_Infrastructure.v
  - COQC Rho_Lemmas.v
  - COQC Rho_Substitution.v
  - COQC Rho_Soundness.v
  - COQC Rho_Examples.v
  -> compiled  proofs.dev
  -> installed proofs.dev
  Done.
```
</details>

#### Alternative: locally compile the Coq proofs
Alternatively, you can also compile the coq proofs yourself by performing the
following actions.

> Depending on your setup, installation might take some time.
> Compiling the Coq proofs takes approximately 20min on an 2.5 GHz Intel Core i7 with 16GB memory.

Make sure you have the correct version of Coq installed. We developed our proofs with Coq version `8.10.2`. The easiest way to compile the proofs is to use Docker and the [Dockerfile](https://github.com/se-tuebingen/oopsla-2022-artifact/blob/main/coq/Dockerfile), which we prepared.

Clone the artifact repository
```
git clone git@github.com:se-tuebingen/oopsla-2022-artifact.git
```

Switch into the correct directory
```
cd oopsla-2022-artifact/coq
```

Build the docker image.
```
docker build -t systemc-proofs-image .
```
This will download the necessary images, which can take a few minutes depending on your connections.
It will take about 5GB of disk space.

Now run the Docker image with the following command:

```
docker run -it --name systemc-proofs-container systemc-proofs-image
```

This will start a shell in the `/home/coq` directory with a copy of the proofs
in `/home/proofs`. The `Dockerimage` already runs all necessary actions
to set up the proofs (that is, `coq_makefile`).

Navigate to the proofs and build them:
```
cd /home/proofs
make
```
Compiling the proofs takes about 20min. In the kick-the-tires phase you can
abort the compilation after seeing initial output like

<details>
```
make[1]: Entering directory '/home/proofs'
COQDEP VFILES
make[1]: Nothing to be done for 'Makefile'.
make[1]: Leaving directory '/home/proofs'
rm -fr html
make[1]: Entering directory '/home/proofs'
"coqc"  -q   -R . Top Util/Taktiks.v
"coqc"  -q   -R . Top Util/FSetNotin.v
"coqc"  -q   -R . Top Util/ListFacts.v
"coqc"  -q   -R . Top Util/FiniteSets.v
"coqc"  -q   -R . Top Util/FSetDecide.v
"coqc"  -q   -R . Top Util/Atom.v
...
```
</details>

#### Cleanup

Run the following commands after quitting the interactive session to
cleanup the docker container and image.

```
docker container rm -f systemc-proofs-container
docker image rm -f systemc-proofs-image
```


## Step-By-Step

### Functional

### Reusable

### Available
We will make our artifact available via Zenodo.