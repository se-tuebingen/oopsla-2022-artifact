## Getting Started

### Kick-the-tires: Demo Website
For the kick-the-tires phase, please perform the following steps, which should not require more than 1-2 minutes:

1. Visit the prepared [artifact website](https://se-tuebingen.github.io/oopsla-2022-artifact/).
   It is hosted on GitHub and will not reveal any information to us.

   (If you want to be sure, you can use a proxy and check the `network` tab in the developer tools. It should only load files from the same website and should not make any additional connections).

   The compiler for System C is compiled to JavaScript and runs in the browser, so please allow scripts to be executed.

2. Visit the [tutorial page](https://se-tuebingen.github.io/oopsla-2022-artifact/tutorial/#repls)
   and click the `run` button on the right. The compiler will be loaded, the example will
   be executed and it should output `"Hello World!\n()"`.

3. Visit the [tutorial page](https://se-tuebingen.github.io/oopsla-2022-artifact/tutorial/index.html#editors)
   and click the `typecheck and run` button on the right. The compiler will be loaded, the example will be type checked. Hover over `println` and check that it shows the type signature.
   Replace the call to `println` with `1 + ""` to introduce a type error and click `typecheck`
   (or \<Cmd\>+Enter / \<Ctrl\>+Enter). A type error should be visible.


#### Optional Alternative: Running the Website Locally
The released artifact comes with a zipped version of the website ([`website.zip`](https://github.com/se-tuebingen/oopsla-2022-artifact/releases/latest/download/website.zip)).
It is packaged as a static website (with JavaScript) and needs to be served
from a local webserver to function correctly.
For the reviewer's convenience, we prepared scripts that start such a web server
Extract the zip file `website.zip`, navigate into the unzipped directory (i.e. `website/`), and
run `start.sh` (on linux) / `start.mac.sh` (on mac) / `start.bat` (on windows).
You should now be able to point your web browser to `http://localhost:8000`.

  > For Linux and Windows users you will need Python 3 to run the demonstration.
  > Python 3 should be installed by default or can be easily installed from
  > your system's package manager or through the Microsoft Store (for Windows users).

If you prefer to use a standard javascript webserver, you can also install
and run one via:

```
npm install -g http-server
cd website/
http-server -p 8000
```


### Kick-the-tires: Coq Proofs
We believe it is not strictly necessary to compile the Coq proofs yourself. Instead,
we have set up continuous integration (GitHub action) to compile the proofs.
As an alternative, we also provide a `Dockerfile` that should simplify compiling
the proofs on your own machine.

Additionally, for the reviewers convenience, we also provide the compiled proofs as a zip file, attached to the release ([`compiled-proofs.zip`](https://github.com/se-tuebingen/oopsla-2022-artifact/releases/latest/download/compiled-proofs.zip)).

#### Alternative 1: Checkout the CI build

To check validity of the proofs, you may visit the [github action](https://github.com/se-tuebingen/oopsla-2022-artifact/actions/workflows/proof-ci.yml) page that contains successful compilation runs of Coq.

For the CI run that corresponds to this release, please visit:

<https://github.com/se-tuebingen/oopsla-2022-artifact/runs/4761043827?check_suite_focus=true#step:4:381>

<details>
To manually navigate to this run, you may select the `build` job and expand `Run coq-community/docker-coq-action@v1`, and finally expand `Build`. You should see the output of `coqc`, which
should look like

```
<><> Processing actions <><><><><><><><><><><><><><><><><><><><><><><><><><><><>
Processing  1/2: [proofs: sh coq_makefile -f _CoqProject -o Makefile]
+ /bin/sh "-c" "coq_makefile -f _CoqProject -o Makefile" (CWD=...)
Processing  1/2: [proofs: make]
+ /usr/bin/make "-j2" (CWD=...)
- COQDEP VFILES
- COQC Util/Taktiks.v
- COQC Util/FSetNotin.v
- COQC Util/ListFacts.v
- COQC Util/FSetDecide.v
- COQC Util/AdditionalTactics.v
- COQC Util/FiniteSets.v
- COQC Util/Atom.v
- COQC Util/Label.v
...
```

</details>

#### Alternative 2: Locally compile Coq proofs
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
