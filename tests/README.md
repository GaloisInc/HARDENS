# End to end runtime verification for RTS

This directory contains the drivers and testcases that implement test scenarios
defined in [](../specs/test_scenarios.lando).

Each scenario is a template, potentially parameterized by a set of variables, as
outlined below.

To run all the tests, just run:

``` sh
python3 ./run_all.py
```

Some tests have a large number of cases. As the implementation and tests
are symmetric, you can do a quick sanity run by setting the `QUICK` environment variable, i.e.:

``` sh
QUICK=1 python3 ./run_all.py
```

## Scenario format

A scenario is a file whose structure is:

  1. An optional list of parameters
  2. A sequence of commands

A command is either a RTS command (such as "M" for setting
maintenance mode) or a regular expression preceeded by the character `?`.

Tests proceed by executing commands one by one. Regular expressions are tested
against the output produced thus far. A test fails if a regular expression fails
to match after a number of retries.


For example, the scenario:

    {T}
    V 0 0 {T}
    V 1 0 {T}

    ?#I 0.*

has one parameter `T`. Next the commands `V 0 0 {T}` and `V 1 0 {T}` are RTS
commands that simulate a temperature sensor reading of the _value_ of the
parameter `T` in both sensors. Finally, the regular expression at the bottom
simply tests that the string `#I 0` is eventually printed to the console.

## "Skipped" tests

This directory includes a set of "skipped" tests. Actually these are scenarios
that may _refine_ those already under `scenarios`. Some of these refinements
require very sophisticated regular expressions to match against, and hence we do
not currently use them for testing.

For example, `exceptional_5{a,b,c,d,e}` describe scenarios where a demultiplexor
fails. One way to check this condition is to look for the warning that two
sensors differ by too large of a value. Another test, that is not quite
equivalent, would be look for a UI state in which at least two sensor values
differ: clearly this is quite a complicated regular expression.
