# frankjnr

Another implementation of the Frank programming language initially based on
the paper ``Do be do be do'' to appear at POPL 2017:

preprint available: https://arxiv.org/abs/1611.09259

#### Installation procedure

To install `frank` the maintained procedure is to use stack ([external
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
--local-bin-path` will display the path).
