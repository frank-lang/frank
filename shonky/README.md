# shonky

This is the repo for a rough-and-ready untyped, hilariously impure, sort-of functional programming language. The key point of it is to support local handling of computational effect, just using the regular application syntax. Application becomes a general means by which one process can coroutine a bunch of subprocesses. It's kind of an untyped version of Frank, and it may yet evolve in that direction. Of course, effectful programming needs dependent types to model the correctness of behaviour with respect to status. But that's another story. Mostly, I just want to improve my kit for building web pages, so although I currently have an interpreter written in Haskell, I might write back ends for JavaScript and for PHP.

## syntax

The basic values are a superficial variant on s-expressions. (In what follows, I write whitespace wherever it is permitted and show by its absence where it is not.)

    a ::= <nonempty sequences of alphanumeric characters>
    
    e ::= 'a                      -- an atom
        | [ ]                     -- the null atom
        | [ e e' ]                -- a cons cell
        
    e' ::= , e e'                 -- list notation for | [ e e' ]
         |                        -- list notation for | []
         | | e                    -- pair notation

However, I'm not in the business of representing computations as values, so I throw in some more gubbins. Programs are built by plugging together n-adic nodes, each of which has n *ports* and one *peg*, and leaves consisting of variables and values.

    e :+= a                       -- a variable
        | e( e , .. )             -- n-adic application
        | e; e                    -- sequencing, taking the value of the second expression
        | e/ e                    -- sequencing, taking the value of the first expression

Note that application associates to the left ("rather as we all did in the '60s", says Roger Hindley) but that ; and / associate to the right, so that if you have a sequence, the value you get is that of the last thing before the first /. It's an impure language, so we sometimes do things just for the hell of it, rather than because we want to know their value. Evaluating s-expressions does the side-effects in left-to-right order. So

    ['get(), 'get(), 'get()]

computes a three element list from the values obtained by issuing the command `'get()` three times in succession.

What is a side-effect? It's just what happens when you apply an *atom*, rather than a *variable* (whose functional meaning will come from the environment). The meaning of the side-effect, or *command* will be determined by an enclosing function.

We have also the means to delay computation by writing n-adic functions (where n can be 0)

    e :+= { e }                   -- 0-adic thunk
        | { h c , .. c }          -- pattern-matching function
        
    h ::=                         -- no effect-handling
        | ( a' , .. ) :           -- declaration of ability to intercept commands on some ports
        
    a' ::=                        -- no more handling
         | a a'                   -- handling a command, and maybe other commands
        
    c ::= ( p , .. ) -> e         -- pattern-matching clause

Functions are defined by a nonempty sequence of pattern-matching clauses. For the most part, we tend just to match on the structure of the values which arrive at a given port. However, we may indicate a *handling* behaviour by saying which commands will be trapped by which ports.

    p ::= { a }                   -- 0-adic thunk pattern (matching values or locally handled commands)
        | { 'a( q , .. ) -> a }   -- command pattern, with patterns for command arguments and a resumption variable
        | q                       -- value pattern
        
    q ::= a                       -- variable matching value
        | 'a                      -- atom matching itself
        | = a                     -- pattern matching value of variable, if variable is an atom
        | [ q q' ]                -- cons cell pattern
   
    q' ::= [ , q q' ]             -- list notation for | [ q q' ]
         |                        -- list notation for | []
         | | q                    -- pair notation

If you offer to intercept particular commands, then you had better do so. A thunk pattern will delay the command (as long as it's one of yours). A command pattern will trap a command matching the given structure arriving on that port, binding a variable to the 1-adic *resumption* that awaits the result of the command.

You can make blocks of (recursive) definitions. We'll need them to do more interesting examples.

    d' ::=
         | d d'
    
    d ::= a -> e                  -- value definition
        | ah ac , ..              -- definition of a handler (where each a repeats the function name)
        | ac , ..                 -- definition of a function (where each a repeats the function name)

You can make a block of local definitions in an expression.

    e :+= {| d' |} e

The functions are considered mutually recursive, but the value definitions are not recursive.

## examples

To test membership of an atom in a list just takes ordinary pattern matching.

    elem(x, [=x| xs]) -> 'tt,
    elem(x, [y| xs])  -> elem(x, xs),
    elem(x, [])       -> 'ff

But to support mutable state requires us to offer interception on a port.

    state(, get set):
    state(s, x)               -> [x, s],
    state(s, {'get() -> k})   -> state(s, k(s)),
    state(s, {'set(t) -> k})  -> state(t, k([]))

We can write a "unix pipe" like this

    pipe(send, recv):
    pipe({f},             x)               -> x,
    pipe({'send(x) -> f}, {'recv() -> g})  -> pipe(f([]), g(x))

Note that the thunk pattern `{f}` traps only value returning and send commands, in accordance with the interception declaration. Meanwhile, the value pattern `x` does not catch *anything*: only the returning of *values*. Correspondingly, the first line does not subsume the second.

If a function runs out of matching clauses, it issues the `'abort()` command. You can catch it like this.

    catch(abort,):
    catch(x,               f) -> x,
    catch({'abort() -> k}, f) -> f()

That's to say the second argument should be a 0-adic thunk which will be invoked only if the first argument aborts.

Your classic conditional is as follows:

    if('tt, t, f) -> t(),
    if('ff, t, f) -> f()

Again, what-to-do-in-each-case is given as a thunk which is forced only as required.

## more later

I have a syntax for string templates with expression splices. I have a corresponding syntax for string patterns with value pattern splices. That's what lets us write parsers and stuff. But I've got to split just now.

## how does it go?

There's a machine. It runs in a loop, building all the control stack information out of data. Resumptions are exactly lumps of stack. Command execution unloads the stack into a resumption until a handler is found.
