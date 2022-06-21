# VeriT Developer Guide

The veriT development repository is currently not publicly available.
Feel free to reach out to us if you would like to have access.

## Compilation veriT for Development

The dependencies required for development are: A C compiler, the autotools
toolchain, *sed*, *lex*, *bison*, and *gmp* (the GNU Multiple Precision
Arithmetic Library).

To build veriT from a fresh clone of the repository run:

```bash
$ autoreconf -i
$ ./configure
$ make
```

Call `make -j` compile on multiple cores in parallel.

`./configure` accepts the option `--enable-debug` to compile in debug
mode.  This mode deactivates optimizations and enables a huge number of
asserts.  When building a non-debug build of veriT, link-time optimization
is relatively slow.  To build veriT without link-time optimization,
but with all optimizations enabled, run `./configure` with the option
`--disable-lto`.

On NixOS the included `shell.nix` file can be used to bring the
development dependencies and some development tools into scope.

## Documentation

## Programming Guidelines

We generally use "[trunk based
development](https://trunkbaseddevelopment.com/)", i.e., development
happens directly on the `master` branch.

There is a CHANGELOG file. Every user facing change must have an entry in
the CHANGELOG file.  Usually in the "Unreleased" section.  Significant
changes that do not directly affect users should still be documented in
the CHANGELOG file.  This is especially relevant if changes affect the
performance characteristic and might indirectly affect users because
the solving time of their benchmarks changes.

Git commit messages can provide context to a change that a pure diff
cannot.  See [this](https://chris.beams.io/posts/git-commit/) blog
post for some useful information on how to write good commit messages.
The gist: the first line should be short, use imperative voice, and not
finish in a colon.  It is followed by an empty line and then additional
information wrapped to a reasonable number of columns.

## Testing Infrastructure

Automated testing of veriT is split into two parts.  Integration tests
test an entire build of veriT on various examples and unit tests test
individual functions.

Integration tests are run by the script `test/run.py`.  It takes one
mandatory argument: the path of a veriT executable and uses Python's
testing system and generates tests automatically.  To do so it collects
the `.smt2` files from `test/examples`, removes some examples that are
in a predefined exclusion list, and executes veriT one each of the
remaining examples.  It tries diffent veriT configurations too.
In addition to this process, `test/run.py` also has some manually defined
tests (in the `veriTTests` class).

Unit tests can be executed by running `make check`.  They use the the
standard autotools testing facilities which compile a binary `veriT-test`
and execute it.  The entry point for this binary is the file `test/main.c`.
The tests are implemented using `test/picotest.h`. 
The [Picotest repository](https://github.com/fredericbonnet/picotest/tree/master/examples)
contains some examples on how this framework works.

In our case we have test suites defined in `test/suites/` and are included
as header in `test/main.c`.  This file also contains the `mainSuite`
that lists the concrete test suites.  Currently, there is one global
fixture `standardEnv` that initializes the veriT DAG with the SMT-LIB
symbols from UF.

Both test parts are automatically run by the CI system.  The CI
configuration can be found in the file `scripts/gitlab-ci.yml`.

## Preparing a Release

## Code Style

We use `clang-format` to automatically format files, but we generally prefer
human judgment over automatic tools.  Hence, one should check the output
`clang-format` manually.  The same idea applies to the guidelines below:
feel free to break them if it improves the readability of the code.

* Code uses a column width of 80. One line comments describing fields and 
  variables can go beyond columns.
* Empty lines are fine, but no excessive spacing. Screen real estate is scarce.
  Hence, no two empty lines between functions etc.
* No tabs shall be used.  Indentation width is *four* spaces.
* Function definitions are separated a newline followed by comment
  `/*--------------------------------------------------------------*/`
  and again a newline
* `__attribute__((noinline))` is on a separate line (`clang-format` does not
  apply this!)
* Declaration of functions might be on a single line (with types on the same line)
 
### Headers

* Library headers occur before local headers.
* One empty line separates library headers from local headers.
* Headers are otherwise listed alphabetically.
* Full path (starting from src) for all local headers is used.

### Types
* Pointers are declared as in: `int *pointer`, without space between `*` and
  the variable name.
* Cast have no space afterwards: `(SAT_Tlit *)malloc(3 * sizeof(SAT_Tlit));`

### Comments
 
Each function declaration is accompanied by a doxygen header of the form
```C
/**
   \author Pascal Fontaine
   \brief get the variable value
   \param var the variable
   \return the value (SAT_VAL_FALSE, SAT_VAL_TRUE, or SAT_VAL_UNDEF)
   \remark this function is linear with respect to the size of the problem */
```
There might be 0, 1, or several remark fields
 
No C++ style (`//`) comments 

Block comments do not contain opening asterisks in each line. The
alignment of the lines is currently three spaces. I.e.
```C
/**
   \brief a function */
int test(int baz)
```
Doxygen is used with Javadoc style comments (`/**` and not `/*!`). With fields
introduced by `\` not `@`. Documentation of members uses `/**< foo */`.
Todos should be marked by ``/* TODO: solve this */``. If they appear inside
Doxygen blocks they can start with `\todo TODO:`. The second `TODO:` aids
search by greping.

Comment banners to structure source files are useful. Those take the form:
```C
/*
  --------------------------------------------------------------
  Core function
  --------------------------------------------------------------
*/
```

