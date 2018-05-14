# Frank

An implementation of the Frank programming language described in the
POPL 2017 paper, ``Do be do be do'' by Sam Lindley, Conor McBride, and Craig
McLaughlin. See the (revised) paper at: https://arxiv.org/abs/1611.09259

Further enhancements are described by Lukas Convent in his MSc thesis of 2017:
http://lukas.convnet.de/proj/master/index.html

#### Installation procedure

The easiest way to install `frank` is to use stack ([external
website](https://www.haskellstack.org),
[github](https://github.com/commercialhaskell/stack)):

```bash
stack setup
```

The above command will setup a sandboxed GHC system with the required
dependencies for the project.

```bash
stack install
```

The above command builds the project locally (`./.stack-work/...`) and then
installs the executable `frank` to the local bin path (executing `stack path
--local-bin` will display the path).

#### Running a Frank program

To run a `frank` program `foo.fk`:

````bash
frank foo.fk
````

By default the entry point is `main`. Alternative entry points can be
selected using the `--entry-point` option.

Some example `frank` programs can be found in `examples`. They should
each be invoked with `--entry-point tXX` for an appropriate number
`XX`. See the source code for details.

To specify a search path for source files use `-I` or `--include=INC`.

Optionally a [shonky](https://github.com/pigworker/shonky) file can be
output with the `--output-shonky` option.

Further debug options are
* `--debug-output`: Enable all debugging facilities
* `--debug-verbose`: Enable verbose variable names etc. on output
* `--debug-tc`: Enable output of type-checking logs

#### Limitations with respect to the paper

 * Only top-level mutually recursive computation bindings are
   supported

 * Coverage checking is not implemented
