# cryptol-verilog

Generation of human-readable verilog from Cryptol source. This package provides
two executables for translating Cryptol programs to Verilog:

- `cryptol-verilogc`, a command-line program that can be used to translate
  Cryptol modules much like a traditional compiler.
- `cryptol-verilog`, which allows the user to load Cryptol modules and translate
  them to Verilog at a Cryptol REPL; and
  
<!-- markdown-toc start - Don't edit this section. Run M-x markdown-toc-refresh-toc -->
**Table of Contents**

- [cryptol-verilog](#cryptol-verilog)
- [Building and Installing cryptol-verilog](#building-and-installing-cryptol-verilog)
- [Repository Structure](#repository-structure)
- [Usage](#usage)
  - [`cryptol-verilog`](#cryptol-verilog)
  - [`cryptol-verilogc`](#cryptol-verilogc)
- [The Translation](#the-translation)
  - [Tested Verilog tools](#tested-verilog-tools)
    - [Tested Versions](#tested-versions)
  - [Translation Strategy](#translation-strategy)
    - [Cryptol and Verilog type correspondence](#cryptol-and-verilog-type-correspondence)
    - [Syntactical Correspondence](#syntactical-correspondence)
    - [Dealing with unsupported features](#dealing-with-unsupported-features)
- [Properties](#properties)
- [Test Harness Generation](#test-harness-generation)
- [Overriding Cryptol library functions](#overriding-cryptol-library-functions)
- [Primitive Verilog Modules](#primitive-verilog-modules)

<!-- markdown-toc end -->
  
  
## Building and Installing cryptol-verilog

After a fresh clone of the repository, initialize the git submodules:

``` sh
git submodule update --init
```

Then build with the standard `cabal` commands:

``` sh
cabal v2-build 
```

You can choose to install the binaries `cryptol-verilog` and `cryptol-verilogc` to the directory `DIR` by running:

``` sh
cabal v2-install --installdir=DIR
```


## Repository Structure

- Haskell library source lives under [./src](./src), the
  `cryptol-verilog` and `cryptol-verilogc` executable wrappers live
  under [./cryptol-verilog](./cryptol-verilog) and
  [./cryptol-verilogc](./cryptol-verilogc) respectively.
- Reference implementations of standard Cryptol libraries and
  primitives live under [./lib/cryptol_verilog](./lib/cryptol_verilog)


## Usage

This repository exposes two executables:

- `crytpol-verilogc`, a CLI tool for translating `cryptol` modules into verilog files
- `cryptol-verilog`, a `Cryptol` REPL extended with additional verilog commands

### `cryptol-verilog`

To load and translate the module `M.cry` in the `cryptol-verilog` REPL:

1. `cabal new-run exe:cryptol-verilog`
2. `:load M.cry`
3. `:verilog M`

This will print the translation of `M` to the screen.

The translation can be controlled using the same options as the command line tool (see below). 

Examples:

- Print the big- and little-endian translations of a module `M`:

    ``` sh
    :load M.cry
    :verilog M --little-endian # or -l
    :verilog M --big-endian    # or -b
    ```

- Write the translation of a module `M` to `M.v` without using System Verilog
  structs:

    ``` sh
    :load M.cry
    :verilog M --de-struct -o M.v
    ```

### `cryptol-verilogc`

To translate a module `M.cry` to `M.sv` using the `cryptol-verilogc` tool:

```
cabal new-run exe:cryptol-verilogc -- M.cry -o M.sv
```

Due to the difference in features supported by different
(System)verilog tools, the compiler exposes more options than the REPL
for controlling the generated verilog.

```
Usage: cryptol-verilogc [OPTIONS] FILE.cry
  -h       --help                                      display this message
  -o FILE  --out=FILE                                  write output to FILE
           --top-level=IDENT                           add top-level Cryptol identifier as a translation target (may be specified multiple times)
  -v       --verbose                                   verbose error output
           --src-locs, --source-locs                   generate source loc comments (default)
           --no-src-locs, --no-source-locs             do not generate source loc comments
  -l       --little-endian                             generate little-endian vectors and arrays
  -b       --big-endian                                generate big-endian vectors and arrays (default)
  -f       --flat-vectors                              flatten multi-dimensional vectors
           --no-flat-vectors                           do not flatten multi-dimensional vectors (default)
  -w       --wrap-arrays                               generate wrappers for modules with multi-dimensional ports
           --no-wrap-arrays                            do not generate wrappers for modules with multi-dimensional ports (default)
  -d       --de-struct                                 generate verilog without struct types
           --no-de-struct                              generate verilog with struct types (default)
  -q       --fully-qualified, --qualified-names        include module path in generation of Verilog module names
           --no-fully-qualified, --no-qualified-names  include module path in generation of Verilog module names (default)
           --specialize                                run type and function specialization pass (default)
           --specialize                                do not run type and function specialization pass
  -V DIR                                               add directory to Verilog source search path
  -r       --reference                                 use reference implementation (ignore library Verilog modules)
           --no-reference                              do not use reference implementation (ignore library Verilog modules) (default)
           --warn-skipped                              print warning message for untranslatable toplevel definitions
           --no-warn-skipped                           do not print warning message for untranslatable toplevel definitions (default)
           --skip-recursive                            try translating only non-recursive toplevel functions (default)
           --no-skip-recursive                         fail if module contains a recursive function
           --simplify-constants                        simplify constants to a value before translation (default)
           --no-simplify-constants                     do not simplify constants to a value before translation
  -t       --explicit-types                            generate SystemVerilog with explicit (var or net) types
           --no-explicit-types                         generate SystemVerilog without explicit (var or net) types (default)
  -p       --param-types                               annotate param declarations with types
           --no-param-types                            do not annotate param declarations with types (default)
           --block-labels                              annotate item blocks with labels
           --no-block-labels                           do not annotate item blocks with labels (default)
  -i       --iverilog-defaults                         set options that work well with iverilog
                                                       (--param-types --no-block-labels --flatten-vectors --no-explicit-types --de-struct --no-formal)
  -y       --yosys-defaults                            set options that work well with Yosys
                                                       (--no-param-types --block-labels --flatten-vectors --no-explicit-types --de-struct)
           --dump-inliner                              dump output of inlining passes
           --dump-finite                               dump output of stream finitizer pass
           --formal                                    generate SVA assertions for Cryptol properties (default)
           --no-formal                                 do not generate SVA assertions for Cryptol properties
           --test=IDENT                                generate tests for the identifier
           --num-tests=NUM                             number of tests to generate
           --test-size=NUM                             size of generated tests
           --test-harness=FILE                         write test harness to FILE (interprets FILE as DIR for 'verilator' backend)
           --sim-backend=IDENT                         simulator backend: 'iverilog' or 'verilator'

Influential environment variables:
    CRYPTOLPATH
        A `:`-separated list of directories to be searched for Cryptol
        modules in addition to the default locations
```

## The Translation

At a high level, `cryptol-verilog` is designed to reliably translate `Cryptol`
functions that may be polymorphic in numeric type parameters, and whose
arguments are sequences, tuples, or records, as these generally have natural
analogs in Verilog. 

Features that are generally _not supported_ include:

- Polymorphic terms (except polymorphism in numeric parameters)
- Recursively-defined terms (see note on streams below)
- Unbounded datatypes (such as `Integer`)
- Higher-order terms

By default, toplevel functions with types that are not supported will be skipped
(and inlined; see below). `--warn-skipped` prints skipped functions to the
console.

### Tested Verilog tools 

The output of `cryptol-verilog` has been evaluated for correctness using
`Verilator`, `Icarus Verilog`, and `Yosys`. For the latter two, SystemVerilog
support must be enabled. 

Given a module `M.cry`, the following flow works well for Icarus:

``` sh
$ cryptol-verilog --iverilog-defaults M.cry -o M.sv
$ iverilog -g2005-sv M.sv
```

And the following works well for Yosys:
``` sh
$ cryptol-verilog --yosys-defaults M.cry -o M.sv
$ yosys -s 'read_verilog -sv M.sv; ...'
```

#### Tested Versions

- Verilator `Verilator 4.108 2021-01-10 rev v4.106-158-g484b76e5b`
- Icarus `Version 11.0`
- Yosys `Yosys 0.9+4228 (git sha1 31562262, clang 10.0.0-4ubuntu1 -fPIC -Os)`

### Translation Strategy 

This section offers a high level description of the Verilog that is generated
for common Cryptol terms.

#### Cryptol and Verilog type correspondence

- Cryptol sequences translate to Verilog `logic` vectors
- Cryptol tuples and records translate to Verilog packed structs
- Cryptol functions translate to Verilog modules

#### Syntactical Correspondence

- Literals of type `[n]`

  These are translated as bitvector literals when `n` is statically known,
  otherwise as a concatenation of literals.

- `if b then e1 else e2` 

  When `b` only includes literals and parameters, this is translated as a generate
  if block, otherwise this is translated using the Verilog conditional operator.

- List comprehensions `[ e | x <- lst ]`, `generate` primitive

  Translated as generate for blocks.

- Function application

  Application of top-level functions become module instantiations. Applications
  of `where`-bound functions are translated by first inlining the function
  definition.


### Dealing with unsupported features

It is often the case that the user may wish to produce a translation of `f` from
module `M`, where `f` depends on `g` and `g` makes use of an unsupported features.

`cryptol-verilog` employs a number of strategies to deal with features that are
not directly supported. 

1. *Specifying desired toplevels*: By default `cryptol-verilog` will attempt to
   translate all functions in a Cryptol module. If only a subset are required,
   the user can specify them with `--top-level`. Only these and their
   dependencies will be translated.

2. *Constant evaluation*: If `g` is a toplevel constant, `cryptol-verilog` will
   try to evaluate it to a value and then produce a Verilog module that returns the
   translation of this value. Thus although the definition of `g` makes use of
   unsupported features, the value may still be translatable.

   Example:

   ```Cryptol
   g : [256][8]
   g = [ helper i | i <- [0..255] ]
     where 
       helper i = if (i > 0) then i + helper (i - 1) else 0
   ```
   
   The translation of `g` is a module that outputs the 256 bytes computed by `g`.

3. *Specialization*: In some cases, `cryptol-verilog` will produce _specialized_
   versions of higher-order functions and polymorphic functions. This may result
   in multiple modules with similar names.
   
   Example:
   
   ```Cryptol
   my_fun : {a} Ring a => a -> a -> a
   my_fun x y = x*y - 2*x*y

   bin_app : {a} (a -> a -> a) -> a -> a -> a
   bin_app f x y = f x y
  
   app_my_fun : [8] -> [8]
   app_my_fun x = bin_app my_fun x x
   ```
   
   is translatable, and will include Verilog definitions of `my_fun` specialized
   to bytes and `bin_app` specialized to bytes and the use of `my_fun` as its
   first argument.

4. *Inlining*: `cryptol-verilog` will inline polymorphic and higher-order terms.
   They will not be included as toplevel modules, but their definitions will be
   available to produce Verilog translations of other terms.
   
   Example:
   
   ```Cryptol
   module Example where 
   
   bin_app : ([8] -> [8] -> [8]) -> [8] -> [8] -> [8]
   bin_app f x y = f x y
   
   my_fun x = bin_app g
     where g a b = a*b
   ```
   
   `my_fun` is translatable, but `bin_app` is not. Translating the `Example` module will result in a Verilog module
   for `my_fun`, but `bin_app` will be skipped.

5. *Heuristics for Integers*: while not directly supported, we do recognize
   `Integer` literals as they are commonly used, for example, in list
   comprehensions or as indices passed to `@` or `!!`.
   
6. *Heuristics for Streams*: `cryptol-verilog` will attempt to transform
   programs that make use of (finite prefixes of) `inf` streams. For example,
   `cryptol-verilog` will support definitions that have the following rough structure:
   
   ```Cryptol
   f : {k} (fin k) => [2][8] -> [k][8]
   f iv = take`{k} out
     where
       out = iv # [ ... | i <- out | ... ] 
   ```
   
   `cryptol-verilog` will try to infer what the finite prefix of the stream is.
   In most cases this is quite obvious: the stream is eventually passed to a
   function like `take`, or is indexed by some integer literal (e.g., `stream @@
   [1, 5, 9]`). If indexed by a word (a value of type `[n]Bit`),
   `cryptol-verilog` may conservatively assume that `2**n-1` elements are
   required, which may result in an impractical Verilog design.

## Properties 

Cryptol programmers typically write _properties_ that they then test or prove to
build confidence in their specifications. `cryptol-verilog` can generate SVA
assertions in the translations Cryptol properties for use by formal tools, e.g. yosys.

Example: in `Inverses.cry`

``` Cryptol
module Inverses where

f : [128][8] -> [128][8]
f xs = reverse xs

property f_inverse xs = f (f xs) == xs
```

``` sh
$ cryptol-verilogc Inverses.cry -o Inverses.sv --formal --yosys-defaults
$ yosys -p 'read_verilog -sv Inverses.sv; hierarchy -auto-top; flatten; sat -prove-asserts'
...
QED
...
```

## Test Harness Generation

`cryptol-verilog` can generate some tests for the translation of Cryptol
function via the `--test` flag. The harness is then suitable for simulation by
simulators like `iverilog`. An alternative `verilator` based harness can be
generated by passing `--sim-backend=verilator`.

Example: in `TestMe.cry`

``` Cryptol
module TestMe where

mux4 : [2] -> [4] -> Bit 
mux4 sel v = v @ sel
```

``` sh
$ cryptol-verilogc TestMe.cry --test=mux4 --num-tests=10 -o Test.sv
$ iverilog -g2005-sv Test.sv && vvp a.out
1
1
1
1
1
1
1
1
1
1
```

Line `i` is a `1` if generated test `i` is correct.

## Overriding Cryptol library functions

Some Cryptol library functions that are expressible in Cryptol are
nevertheless implemented as builtins for performance. 

To provide a basis for translation to Verilog, it is convenient to use
reference Cryptol implementations. `cryptol-verilog` allows the user
to provide modules containing reference definitions of terms for use
in Verilog translation.

For example, `pmod` is built in to the implementation of Cryptol. In
order to provide a reference implementation of `pmod` that can be used
during translation, we can write a module `Cryptol::Overrides` that
exports `pmod` with the same type signature as `pmod` exported by
`Cryptol`. When `cryptol-verilog` is invoked to translate a module
`M`, any references to `Cryptol::pmod` will be replaced with
`Cryptol::Overrides::pmod`. 

`cryptol-verilogc` will look for overrides in [lib/cryptol-verilog/overrides](lib/cryptol-verilog/overrides).

## Primitive Verilog Modules

`cryptol-verilog` allows the user to provide their own Verilog modules
as translations for given `Cryptol` definitions.

It is possible to supply hand-written Verilog modules to be used as
the translation of a given Cryptol declaration. 

See [here](examples/clocking) for an example of how this can be used with pipelined,
clocked designs.

The user must provide a docstring indicating:
1. The source file containing a module with *the same name* as the
   `Cryptol` declaration; and
2. The names of the input ports of the Verilog module.

These requirements are satisfied via the following syntax:

``` Cryptol
/** 
  @cryptol-verilog-primitive FileName.v 
  @cryptol-verilog-inputs name1 name2 ...
*/
primitive f : t1 -> t2 -> ... -> t 
```

The Verilog module *must* have a single output port with the name
"out".

The declaration can either be marked `primitive`, or can be given a
definition to be used as a reference implementation.

Example: In `ForeignVerilog.cry`

 ``` Cryptol
/** 
  @cryptol-verilog-primitive AnExternalModule.v 
  @cryptol-verilog-inputs signal1 signal2
*/
primitive AnExternalModule : {k} (fin k) => [k] -> [k] -> [k]
 ```

or alternatively

 ``` Cryptol
/** 
  @cryptol-verilog-primitive AnExternalModule.v 
  @cryptol-verilog-inputs signal1 signal2
*/
AnExternalModule : {k} (fin k) => [k] -> [k] -> [k]
AnExternalModule x y = x + y
```

In `AnExternalModule.v`:

``` Verilog
module AnExternalModule
  #(parameter k = 1)
   (input  logic [k-1:0] signal1,
    input logic [k-1:0]  signal2,
    output logic [k-1:0] out);
   assign out = signal1 + signal2;
endmodule
```

At the moment, only sequences (and bits) are supported as input/output types
(i.e., no records or tuples).
