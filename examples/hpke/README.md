# Analysing the HPKE Standard – Supplementary Material

The material in this directory is supplementary material accompanying the paper:

Joël Alwen, Bruno Blanchet, Eduard Hauck, Eike Kiltz, Benjamin Lipp,
and Doreen Riepel. Analysing the HPKE Standard. In Anne Canteaut and
Francois-Xavier Standaert, editors, Eurocrypt 2021, Lecture Notes in
Computer Science, Zagreb, Croatia, October 2021. Springer. To appear.
Long version: https://eprint.iacr.org/2020/1499 

## Preliminaries

The “RFC” we are referring to in this README, is
[the draft 8 of the RFC “Hybrid Public Key Encryption”](https://www.ietf.org/id/draft-irtf-cfrg-hpke-08.html).

## Files in this Directory

### Library Files

The files with filenames starting by `lib.*` contain macro definitions
for CryptoVerif:

- `lib.authkem.ocvl`: assumptions on authenticated KEMs as defined
  in the paper
- `lib.gdh.ocvl`: the GDH assumption as used by the paper. This is a
  simplified version of the GDH assumption available in the standard
  CryptoVerif library, with just the oracles needed for our proofs.
- `lib.aead.ocvl`: defines an AEAD scheme, with multikey security notions.
- `lib.prf.ocvl`: defines a PRF, with a multikey security notion.
- `lib.choice.ocvl`: defines convenience functions to choose between
  plaintexts m0 and m1 based on a bit b.
- `lib.option.ocvl`: defines a macro for option types, which we heavily
  use as return types of functions
- `lib.truncate.ocvl`: defines an equivalence for transforming a
  uniformly distributed random value of one type into a uniformly
  distributed random value of another, shorter, type.

### Common Definitions

The files with filenames starting by `common.*` contain definitions
used in multiple models:

- `common.dhkem.dh.ocvl`: definition of the Diffie-Hellman group for
  all DHKEM security notions
- `common.dhkem.ocvl`: definition of DHKEM as defined in the RFC
- `common.hpke.ocvl`: definition of HPKE (only everything after the KEM)
  as defined in the RFC

These files are included by the `*.m4.ocv` files that generate the model files.

### Model Files

The ”model files” are the files on which we run CryptoVerif. Each model
contains the definition of a security notion, the definition of the
game, and the proof.

We prove three security notions for DHKEM, and three security notions
for HPKE. These three files share a lot of code, which is why we generate
the files from templates. These templates are the `*.m4.ocv` files; m4
makes reference to the preprocessor m4 which we use.

To generate the model files from the templates, run the script `prepare`
in this directory.

#### Which files to read

If you don't mind jumping around in one big file, you can read the
`*.ocv` files listed below.

If you prefer smaller files, you can read the `*.m4.ocv` files for
an overview, and look at the included files separately.

#### DHKEM

- `dhkem.auth.outsider-cca-lr.ocv`: Prove that DHKEM as defined in the
  RFC is Outsider-CCA-secure.
- `dhkem.auth.outsider-auth-lr.ocv`: Prove that DHKEM as defined in the
  RFC is Outsider-Auth-secure.
- `dhkem.auth.insider-cca-lr.ocv`: Prove that DHKEM as defined in the
  RFC is Insider-CCA-secure.

#### KeySchedule

We do not use a template for this proof, because it is the only one of
its kind.

- `keyschedule.auth.prf.ocv`: Prove that the key schedule `KS_auth()` as
  used by HPKE's mode Auth, is a PRF with `shared_secret` as key.

#### HPKE Composition Proofs

These models treat HPKE as defined in the RFC, assuming
- KeySchedule (without the VerifyPSKInputs call) is a PRF with
  `shared_secret` as key
- the KEM used is an authenticated KEM satisfying the appropriate
  above-mentioned security notions

There is one model for each security notion:

- `hpke.auth.outsider-cca.ocv`: Prove that HPKE is Outsider-CCA-secure.
- `hpke.auth.outsider-auth.ocv`: Prove that HPKE is Outsider-Auth-secure.
- `hpke.auth.insider-cca.ocv`: Prove that HPKE is Insider-CCA-secure.
