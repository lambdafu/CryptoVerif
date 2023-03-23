# cv2fstar

## Directory Overview

* `cv2fstar`: F\* framework for cv2fstar
* `nspk`: first example using cv2fstar

## Prerequisites for running the parts involving CryptoVerif

The following environment variable is recommended:

* `CRYPTOVERIF` set to a directory containing a `cryptoverif` binary,
  ideally the `CryptoVerif` directory in this repository.


## Prerequisites for running the parts involving F\*

You need to have the F\* language (https://fstar-lang.org/) and the
HACL\* cryptographic library (https://github.com/hacl-star/hacl-star)
installed.
You need to use a recent version of OCaml (>= 4.08).
You first need to have opam installed (https://opam.ocaml.org/).
Then you can install F\* and HACL\* by running
```
  git clone https://github.com/project-everest/everest.git
  cd everest
  ./everest check
  # The command above checks that the environment is ok.
  # Accept installing missing opam packages if it asks for it
  # and/or follow the instructions it gives for installing
  # missing packages and rerun until it succeeds.
  ./everest pull
  ./everest -j <number of threads> make
  # Some proofs in HACL* are fragile. You may need to rerun
  # the command above until it succeeds. If you get an error
  # message about the .NET framework, install the version of
  # .NET that it requires before rerunning.
```
You need the following environment variables:

* `CV2FSTAR_HOME` set to the absolute path of the directory `cv2fstar`
* `PROJECT_HOME` set to the absolute path of the directory `nspk`
* And all environment variables needed for an F\* and HACL\* setup.

Suggestions: Use something like [direnv](https://direnv.net/) to make
that easier on a per-project basis. Example `.envrc` file for this
project:

```
export CRYPTOVERIF=~/workspace/cryptoverif
export EVEREST_HOME=~/workspace/everest

export CV2FSTAR_HOME=$CRYPTOVERIF/cv2fstar/cv2fstar
export PROJECT_HOME=$CRYPTOVERIF/cv2fstar/nspk

export EVEREST_ENV_DEST_FILE=$EVEREST_HOME/.envrc

export FSTAR_HOME=$EVEREST_HOME/FStar
export FSTAR=${FSTAR_HOME}/bin/fstar.exe
export KRML_HOME=$EVEREST_HOME/karamel
export HACL_HOME=$EVEREST_HOME/hacl-star
# The everest script should note this at the end
export Z3_HOME=$EVEREST_HOME/z3
# The everest script should note this at the end
export MLCRYPTO_HOME=$EVEREST_HOME/MLCrypto
export OPENSSL_HOME=$EVEREST_HOME/MLCrypto/openssl
export VALE_HOME=$EVEREST_HOME/vale
export LD_LIBRARY_PATH=$EVEREST_HOME/MLCrypto/openssl

export PATH=$Z3_HOME/bin:$FSTAR_HOME/bin:$KRML_HOME:$PATH

# These lines automatically added by ./everest
export EVEREST_SCONS_CACHE_DIR=/tmp/everest
```

## Use cv2fstar with an example

* in `cv2fstar`, run `make`. This produces a library file.
* in `nspk`, run `../../cryptoverif -impl FStar -o src nsl.ocv`.
  This generates `fsti` and `fst` files in the directory `src`
* in `nspk`, run `make`. This typechecks the FStar code,
  extracts to OCaml, runs the test and displays its output.
* the file `nspk/execution` gives the output of a sample execution.
