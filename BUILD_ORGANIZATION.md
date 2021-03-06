# HOW TO BUILD:

1. Make sure you have the right version of Coq.  
   ```sh
   grep ^COQVERSION Makefile
   ```
   will tell you which versions are compatible.

2. Make sure you have the right version of CompCert.
   VST 1.9 uses CompCert 2.7.2 for Coq 8.6.1 or Coq 8.7.

   However, [AbsInt.com](https://www.absint.com) (the official distributor of
   CompCert) does not support CompCert 2.7 for Coq 8.6 (only for 8.4 and 8.5).

   The version of CompCert 2.7 for Coq 8.6/8.7 is this _unofficial_ port:  
   https://github.com/ildyria/CompCert/tree/v2.7.2  
   For example, you could download and unpack this zip file:  
   https://github.com/ildyria/CompCert/archive/v2.7.2.3.zip  
   OR
   ```sh
   git clone https://github.com/ildyria/CompCert;
   git checkout v2.7.2
   ```

### METHOD A [recommended]

This method bases the VST on a copy of certain CompCert specification files
distributed with VST, located in `VST/compcert`.

1. Execute this command:
   ```
   make
   ```  
   (or, if you have a multicore computer,  `make -j`)
2. *optional, only if you're going to run "clightgen"*  
    Unpack CompCert in the location of your choice (not under VST/), and in that
    directory,  
    ```
    make clightgen
    ```

### METHOD B [alternate]

This method bases the VST on the same specification files
that the CompCert compiler is built upon (in contrast to method A,
which uses verbatim copies of them).

1. Unpack CompCert in a sibling directory to VST;  
   in that directory, build CompCert according to the instructions
   ```sh
    ./configure -clightgen ia32-linux;
    make
    ```
2. In the VST directory, create a file `CONFIGURE` containing exactly the text:  
   ```
   COMPCERT=../CompCert   # or whatever is your path to compcert
   ```
3. In the VST directory,  
   ```sh
   make
   ```

Note on the Windows (cygwin) installation of CompCert:
To build CompCert you'll need an up to date version of the
menhir parser generator: http://gallium.inria.fr/~fpottier/menhir/
To work around a cygwin incompatibility in the menhir build,
`touch src/.versioncheck` before doing `make`.

--------------------------------------------------------------------------------

# ORGANIZATION:

The Verified Software Toolchain is organized into separate subprojects,
each in a separate directory:

- `msl` -   Mechanized Software Library
- `examples` - examples of how to use the msl (not ported to Coq 8.6)
- `compcert` -   front end of the CompCert compiler, specification of C light
- `sepcomp` - the theory and practice of how to specify shared-memory interaction
- `veric` -  program logic (and soundness proof) for Verifiable C
- `floyd` -  tactics for applying the separation logic
- `progs` -  sample programs, with their verifications

The dependencies are:

- `msl`:   _no dependency on other directories_
- `examples`: msl
- `compcert`: _no dependency on other directories_
- `sepcomp`: compcert
- `veric`:  msl compcert sepcomp
- `floyd`: msl sepcomp compcert veric
- `progs`: msl sepcomp compcert veric floyd

In general, we Import using `-Q` (qualified) instead of `-R`
(recursive).  This means modules need to be named using qualified names.
Thus, in `veric/expr.v` we write `Require Import msl.msl_standard`
instead of `Require Import msl_standard`.  To make this work, the loadpaths
need to be set up properly; the file `.loadpath` (built by `make .loadpath`)
shows what -I includes to use.

## USING VST:

To use either of these interactive development environments you will
need to have the right load path.  This can be done by command-line
arguments to coqide or coqtop.  The precise command-line arguments
to use when running CoqIDE or coqc are constructed automatically when
when you do "make", in the following files:

- `.loadpath-export`: For VST users, running the IDE outside the VST directory
- `.loadpath` : For VST developers, running the IDE in the VST directory
- `_CoqProject-export`: identical to `.loadpath-export`
- `_CoqProject`: identical to `.loadpath`

#### WITH COQIDE

From the VST root directory, run `./coqide` to run coqide with recommended options.
(Read the script for more info.)

#### WITH PROOF GENERAL

There are three methods in which to configure Proof General.

1. **Obsolete and not maintained.**  
   On Linux systems, use the provided `VST/pg` script, as follows:  
   ```
   ./pg
   ```  
   This script is adapted from the CompCert project. It starts
   emacs+Proof General with the load path arguments specified in
   the generated `.loadpath` file.
2. Use the `_CoqProject` file generated by the Makefile
   to get the same information that's in the `.loadpath`.
   (Yes, we know, normally it's the other way 'round, normally one generates
    a Makefile from the `_CoqProject`.)

## NEW DIRECTORIES:

If you add a new directory, you will probably want to augment the loadpath
so that qualified names work right.  Edit the `OTHERDIRS` or `VSTDIRS` lines of
the `Makefile`.

## EXTERNAL COMPCERT:

The VST imports from the CompCert verified C compiler, the definition
of C light syntax and operational semantics.  For the convenience of
VST users, the `VST/compcert` directory is a copy (with permission) of
the front-end portions of compcert.  
You may choose to ignore the `VST/compcert` directory and have
the VST import from a build of compcert that you have installed in
another directory, for example,  `../CompCert`.

**This has not been tested recently, as of August 2017.**  
To do this, create a file `CONFIGURE` containing a definition such as,
  `COMPCERT=../CompCert`  
Make sure that you have the right version of CompCert!  Check
the file `VST/compcert/VERSION` to be sure.
