module Shonky.Semantics where

import Control.Monad
import Debug.Trace
import System.IO
import Data.IORef
import Data.List

import qualified Data.Map.Strict as M

import Shonky.Syntax

-- There is no predefined Show instance
instance Show (IORef a) where
  show _ = "<ioref>"

data Val
  = VA String                        -- atom
  | VI Integer                       -- integer
  | Val :&& Val                      -- cons
  | VX String                        -- string
  | VF Env [[String]] [([Pat], Exp)] -- function (anonymous)
  | VB String Env                    -- built-in function
  | VC Comp                          -- comp
  | VR (IORef Val)                   -- reference cell
  | VK SkippedAgenda                 -- continuation
  deriving Show

-- comp: value or command call
data Comp
  = Ret Val                          -- value
  | Call String [Val] Agenda         -- command call: cmd-id, values, suspended agenda
  deriving Show

-- stack of (collections of definitions)
data Env
  = Env :/ [Def Val]
  | Empty
  deriving Show

data Frame
  = Car Env Exp                                   -- head can be processed. env, uncomputed tail are recorded
  | Cdr Val                                       -- tail can be processed. computed head is recorded
  | Fun Env [Exp]                                 -- operator can be processed. env, operands are recorded
  | Arg [String] Val [Comp] Env [[String]] [Exp]  -- current arg can be processed.
                                                  --     [String]   handleable commands of current arg
                                                  --          Val   eval. handler
                                                  --       [Comp]   eval. args (reversed)
                                                  --          Env   environment
                                                  --   [[String]]   handleable commands
                                                  --        [Exp]   non-eval. args
  | Seq Env Exp                                   -- 1st exp can be processed. env, 2nd exp is recorded
  | Qes Env Exp                                   -- 1st exp can be processed. env, 2nd exp is recorded
  | Qed Val
  | Def Env [Def Val] String [Def Exp] Exp
  | Txt Env [Char] [Either Char Exp]              -- current char of string can be processed. env, already computed reversed beginning, rest are recorded
  deriving Show

type Agenda = ([Frame], [String])
-- [Frame]:         Frame stack
-- [String]: `cts`  Commands to be skipped. Represents multiset.

type SkippedAgenda = ([Frame], [String])
-- [Frame]:         Skipped frames (chronological order)
-- [String]: `cas`  Commands that were already skipped. Represents multiset.

-- This pretty-printer more-or-less does the right thing for rendering
-- Frank values encoded in shonky.
--
-- One thing it still gets wrong is printing 'nil' for an empty
-- string, because it does not know the type.
--
-- Another problem is that for complex values (including computations)
-- it resorts to invoking show.

ppVal :: Val -> String
ppVal (VA s)                           = "'" ++ s   -- TODO: error message here?
ppVal (VI n)                           = show n
ppVal (VX [c])                         = "'" ++ [c] ++ "'"
ppVal v@(VA "cons" :&& (VX [_] :&& _)) = "\"" ++ ppStringVal v ++ "\""
ppVal (VA "cons" :&& (v :&& w))        = "[" ++ ppVal v ++ ppListVal w ++ "]"
ppVal (VA "nil" :&& _)                 = "[]"
ppVal (VA k :&& v)                     = k ++ ppConsArgs v
ppVal v                                = "[COMPLEX VALUE: " ++ show v ++ "]"

-- parentheses if necessary
ppValp :: Val -> String
ppValp v@(VA "cons" :&& (VX [_] :&& _)) = ppVal v   -- string
ppValp v@(VA _ :&& VA "")               = ppVal v   -- nullary constructor
ppValp v@(VA _ :&& _)                   = "(" ++ ppVal v ++ ")"
ppValp v                                = ppVal v

ppConsArgs :: Val -> String
ppConsArgs (v :&& w) = " " ++ ppValp v ++ ppConsArgs w
ppConsArgs (VA "")   = ""
ppConsArgs v         = "[BROKEN CONSTRUCTOR ARGUMENTS: " ++ ppVal v ++ "]"

ppStringVal :: Val -> String
ppStringVal (v :&& VA "")                  = ppStringVal v
ppStringVal (VA "cons" :&& (VX [c] :&& v)) = c : ppStringVal v
ppStringVal (VA "nil")                     = ""
ppStringVal v                              = "[BROKEN STRING: " ++ ppVal v ++ "]"

ppListVal :: Val -> String
ppListVal (v :&& VA "")             = ppListVal v
ppListVal (VA "cons" :&& (v :&& w)) = ", " ++ ppVal v ++ ppListVal w
ppListVal (VA "nil")                = ""
ppListVal v                         = "[BROKEN LIST: " ++ ppVal v ++ "]"

-- Given env and 2 operands (that are values), compute result
plus :: Env -> [Comp] -> Val
plus g [a1,a2] = VI (f a1 + f a2)
  where f x = case x of
          Ret (VI n) -> n
          _ -> error "plus: argument not an integer"
plus g _ = error "plus: incorrect number of arguments, expected 2."

minus :: Env -> [Comp] -> Val
minus g [a1,a2] = VI (f a1 - f a2)
  where f x = case x of
          Ret (VI n) -> n
          _ -> error "minus: argument not an integer"
minus g _ = error "minus: incorrect number of arguments, expected 2."

builtins :: M.Map String (Env -> [Comp] -> Val)
builtins = M.fromList [("plus", plus), ("minus", minus)]

-- Look-up a definition
fetch :: Env -> String -> Val
fetch g y = go g where
  go h@(g' :/ ds) = defetch ds where
    defetch [] = go g'
    defetch ((x := v) : ds)
      | x == y = v
      | otherwise = defetch ds
    defetch (DF x hss pes : ds)
      | M.member x builtins && x == y = VB x h
      | x == y = VF h hss pes
      | otherwise = defetch ds
  go _ = error $ concat ["fetch ",y,show g]

-- High-level computation functions that return a Comp (either Val or command call):
--   compute, consume, define, combine, args, command, tryRules
-- Most of them take an Env and maintain an agenda (frame stack, commands-to-be-skipped).

-- Given env `g` and framestack `ls`, compute expression.
-- 1) Terminating exp: Feed value into top frame
-- 2) Ongoing exp:     Create new frame
compute :: Env -> Exp -> Agenda -> Comp
compute g (EV x)       (ls, sc) = consume (fetch g x) (ls, sc)       -- 1) look-up value
compute g (EA a)       (ls, sc) = consume (VA a) (ls, sc)            -- 1) feed atom
compute g (EI n)       (ls, sc) = consume (VI n) (ls, sc)            -- 1) feed int
compute g (a :& d)     (ls, sc) = compute g a (Car g d : ls, sc)     -- 2) compute head. save tail for later.
compute g (f :$ as)    (ls, sc) = compute g f (Fun g as : ls, sc)    -- 2) Application. Compute function. Save args for later.
compute g (e :! f)     (ls, sc) = compute g e (Seq g f : ls, sc)     -- 2) Sequence.    Compute 1st exp.  Save 2nd for later.
compute g (e :// f)    (ls, sc) = compute g e (Qes g f : ls, sc)     -- 2) Composition. compute 1st exp.  save 2nd for later.
compute g (EF hss pes) (ls, sc) = consume (VF g hss pes) (ls, sc)    -- 1) feed in function
compute g (ds :- e)    (ls, sc) = define g [] ds e (ls, sc)          -- (not used by Frank)
compute g (EX ces)     (ls, sc) = combine g [] ces (ls, sc)          -- 2) compute string

-- Take val `v` and top-frame from stack, apply it to `v` in
consume :: Val -> Agenda -> Comp
consume v (Car g d             : ls, sc) = compute g d (Cdr v : ls, sc)               -- Given: eval. head `v`,     non-eval. tail `d`.  Record `v` and compute tail `d`.
consume v (Cdr u               : ls, sc) = consume (simplStr u v) (ls, sc)            -- Given: eval. head `u`,     eval.     tail `v`.  Put together.
consume v (Fun g as            : ls, sc) = args v [] g (handles v) as (ls, sc)        -- Given: eval. function `v`, non-eval. args `as`. Compute `as`, then feed them into `v`
consume v (Arg _ f cs g hss es : ls, sc) = args f (Ret v : cs) g hss es (ls, sc)      -- Given: Eval.:     handler `f`,
                                                                                      --                   first args `cs` (reversed),
                                                                                      --                   current arg `v`
                                                                                      --        Non-eval.: last args `es`
                                                                                      -- Add `v` to `cs` and re-call `args`
consume _ (Seq g e             : ls, sc) = compute g e (ls, sc)                       -- Sequence.    Given: eval. 1st _,   non-eval. 2nd `e`. Compute `e`.
consume v (Qes g e             : ls, sc) = compute g e (Qed v : ls, sc)               -- Composition. Given: eval. 1st `v`, non-eval. 2nd `e`. Record `v` and compute `e`.
consume _ (Qed v               : ls, sc) = consume v (ls, sc)                         -- LC: Bug here? Why discard argument? (but not used by Frank so far anyway)
consume v (Def g dvs x des e   : ls, sc) = define g ((x := v) : dvs) des e (ls, sc)   -- (not used by Frank)
consume v (Txt g cs ces        : ls, sc) = combine g (revapp (txt v) cs) ces (ls, sc) -- (not used by Frank)
consume v ([], sc)                         = Ret v

-- inch and ouch commands in the IO monad
ioHandler :: Comp -> IO Val
ioHandler (Ret v) = return v
ioHandler (Call "inch" [] (ks, sc)) =
  do c <- getChar
     -- HACK: for some reason backspace seems to produce '\DEL' instead of '\b'
     let c' = if c == '\DEL' then '\b' else c
     ioHandler (consume (VX [c']) (reverse ks, sc))
ioHandler comp@(Call "ouch" [VX [c]] (ks, sc)) =
  do putChar c
     hFlush stdout
     ioHandler (consume (VA "unit" :&& VA "") (reverse ks, sc))
ioHandler (Call "new" [v] (ks, sc)) =
  do ref <- newIORef v
     ioHandler (consume (VR ref) (reverse ks, sc))
ioHandler (Call "write" [VR ref, v] (ks, sc)) =
  do writeIORef ref v
     ioHandler (consume (VA "unit" :&& VA "") (reverse ks, sc))
ioHandler (Call "read" [VR ref] (ks, sc)) =
  do v <- readIORef ref
     ioHandler (consume v (reverse ks, sc))
ioHandler (Call c vs ks) = error $ "Unhandled command: " ++ c ++ concat (map (\v -> " " ++ ppVal v) vs)

-- A helper to simplify strings (list of characters)
-- this allows regular list append [x|xs] to function like [|`x``xs`|] but
-- only for string arguments.
simplStr :: Val -> Val -> Val
simplStr (VX x) (VA "") = VX x -- appending the empty string
simplStr (VX x) (VX y) = VX (x ++ y)
simplStr u v  = u :&& v -- no simplification possible

-- xz `revapp` ys = reverse xz ++ ys
revapp :: [x] -> [x] -> [x]
revapp xz ys = foldl (flip (:)) ys xz

reassembleAgenda :: SkippedAgenda -> Agenda -> Agenda
reassembleAgenda (ks, cas) (ls, cts) = (ks `revapp` ls, cas ++ cts)

-- evaluate string of type [Either Char Exp]
-- given: env, already computed reversed beginning, rest, frame stack
combine :: Env -> [Char] -> [Either Char Exp] -> Agenda -> Comp
combine g cs [] (ls, sc) = consume (VX (reverse cs)) (ls, sc)
combine g cs (Left c  : ces) (ls, sc) = combine g (c : cs) ces (ls, sc)
combine g cs (Right e : ces) (ls, sc) = compute g e (Txt g cs ces : ls, sc)

-- (not used in Frank)
define :: Env -> [Def Val] -> [Def Exp] -> Exp -> Agenda -> Comp
define g dvs [] e (ls, sc) = compute (g :/ reverse dvs) e (ls, sc)
define g dvs (DF f hss pes : des) e (ls, sc) =
  define g (DF f hss pes : dvs) des e (ls, sc)
define g dvs ((x := d) : des) e (ls, sc) =
  compute (g :/ revapp dvs (defo des)) d (Def g dvs x des e : ls, sc)
  where
    defo (DF f hss pes : des) = DF f hss pes : defo des
    defo (_ : des)            = defo des
    defo []                   = []

-- Return handleable commands
handles :: Val -> [[String]]
handles (VF _ hss _) = hss
handles _ = []

-- given: eval. operator `f`, eval. reversed arguments `cs`, env `g`,
--        handleable commands, non-eval. args `es`, frame stack
-- Compute until all [Exp] are [Comp], then call `apply`.
args :: Val -> [Comp] -> Env -> [[String]] -> [Exp] -> Agenda -> Comp
args f cs g hss [] (ls, sc) = apply f (reverse cs) (ls, sc)                               -- apply when all args are evaluated
args f cs g [] es (ls, sc) = args f cs g [[]] es (ls, sc)                                 -- default to [] (no handleable commands) if not explicit
args f cs g (hs : hss) (e : es) (ls, sc) = compute g e (Arg hs f cs g hss es : ls, sc)    -- compute argument, record rest. will return eventually here.

-- `apply` is called by `args` when all arguments are evaluated
-- given: eval. operator, eval. args, frame stack
apply :: Val -> [Comp] -> Agenda -> Comp
apply (VF g _ pes) cs (ls, sc) = tryRules g pes cs (ls, sc)                       -- apply function to evaluated args `cs`
apply (VB x g) cs (ls, sc) = case M.lookup x builtins of                          -- apply built-in fct. to evaluated args `cs`
  Just f -> consume (f g cs) (ls, sc)
  Nothing -> error $ concat ["apply: ", x, " not a builtin"]
apply (VA a) cs (ls, sc) =                                                        -- apply a command to evaluated args `cs`
  -- commands are not handlers, so the cs must all be values
  command a (map (\ (Ret v) -> v) cs) ([], []) (ls, sc)
apply (VC (Ret v)) [] (ls, sc) = consume v (ls, sc)                               -- apply a value-thunk to 0 args (force)
apply (VC (Call a vs (ks, cas))) [] (ls, cts) = command a vs (ks, cas) (ls, cts)  -- apply a command-thunk to 0 args (force)
apply (VK sag) [Ret v] ag = consume v (reassembleAgenda sag ag)                   -- execute a continuation by providing return value:
apply f cs (ls, sc) = error $ concat ["apply: ", show f, show cs, show ls]

-- given: cmd-id, args, skipped agenda, current agenda
-- Assign command-request to a handler (fix argument) and continue with `args`.
-- If there is no handler, just return a `Call` (comp. is stuck)
command :: String -> [Val] -> SkippedAgenda -> Agenda -> Comp
command c vs (ks, cas) ([], _) = Call c vs (ks, cas)                        -- if agenda is done (i.e. no handler there), return Call
command c vs (ks, cas) (Arg hs f cs g hss es : ls, cts)                     -- if there is a handler that can handle `c` and `c` is not to be skipped,
  | elem c hs && not (elem c cts) = args f (Call c vs (ks, cas) : cs) g hss es (ls, cts)  --   fix argument and continue with `args`
command c vs (ks, cas) (k@(Arg hs f cs g hss es) : ls, cts)                 -- if there is a handler that can handle `c` and `c` is to be skipped,
  | elem c hs && elem c cts = command c vs (k : ks, c : cas) (ls, delete c cts)           --   ignore current handler `k`, remove one `c` from `sc'` and recurse
command c vs (ks, cas) (k : ls, cts) = command c vs (k : ks, cas) (ls, cts) -- else recurse

-- given:  env, rules, evaluated args, frame stack
-- selects first rule that matches and computes that expression
tryRules :: Env -> [([Pat], Exp)] -> [Comp] -> Agenda -> Comp
tryRules g [] cs (ls, sc) = command "abort" [] ([], []) (ls, sc)            -- no rule matches
tryRules g ((ps, e) : pes) cs (ls, sc) = case matches g ps cs of
  Just g  -> compute g e (ls, sc)                                           -- rule matches, compute
  Nothing -> tryRules g pes cs (ls, sc)                                     -- rule fails, try next

-- given:   env `g`, list of patterns, list of comps
-- returns: `g` extended by bindings on match
matches :: Env -> [Pat] -> [Comp] -> Maybe Env
matches g [] [] = return g
matches g (p : ps) (c : cs) = do
  g <- match g p c
  matches g ps cs
matches _ _ _ = Nothing

-- given:   env `g`, pattern, comp
-- returns: `g` extended by bindings on match
match :: Env -> Pat -> Comp -> Maybe Env
match g (PV q) (Ret v) = vmatch g q v         -- value matching, no binding
match g (PT x) c = return (g :/ [x := VC c])  -- variable binding
match g (PC c qs x) (Call c' vs ks) = do      -- command call matching: cmd parameters `vs`, continuation (future agenda)
  guard (c == c')
  g <- vmatches g qs vs
  return (g :/ [x := VK ks])  -- bind continuation var `x` to future agenda
match _ _ _ = Nothing

vmatches :: Env -> [VPat] -> [Val] -> Maybe Env
vmatches g [] [] = return g
vmatches g (q : qs) (v : vs) = do
  g <- vmatch g q v
  vmatches g qs vs
vmatches _ _ _ = Nothing

vmatch :: Env -> VPat -> Val -> Maybe Env
vmatch g (VPV x) v = return (g :/ [x := v])
vmatch g (VPI n) (VI m) | n == m = return g
vmatch g (VPA a) (VA b) | a == b = return g
vmatch g (q :&: q') (v :&& v') = do
  g <- vmatch g q v
  vmatch g q' v'
vmatch g (VPQ x) v | txt (fetch g x) == txt v = return g
vmatch g q (VX cs) = do
  (g, []) <- xmatch g q cs
  return g
vmatch _ _ _ = Nothing

xmatch :: Env -> VPat -> String -> Maybe (Env, String)
xmatch g (VPV x) (c : cs) = return (g :/ [x := VX [c]], cs)
xmatch g (VPA a) cs = do
  cs <- snarf (VA a) cs
  return (g, cs)
xmatch g (q :&: q') cs = do
  (g, cs) <- xmatch g q cs
  g <- vmatch g q' (VX cs)
  return (g, [])
xmatch g (VPQ x) cs = do
  cs <- snarf (fetch g x) cs
  return (g, cs)
xmatch g (VPX []) cs = return (g, cs)
xmatch g (VPX (Left c : cqs)) (c' : cs)
  | c == c' = xmatch g (VPX cqs) cs
xmatch g (VPX [Right q]) cs = do
  g <- vmatch g q (VX cs)
  return (g, [])
xmatch g (VPX (Right q : cqs)) cs = do
  (g, cs) <- xmatch g q cs
  xmatch g (VPX cqs) cs
xmatch _ _ _ = Nothing

snarf :: Val -> String -> Maybe String
snarf (VA a) cs = unpref a cs
snarf (u :&& v) cs = do
  cs <- snarf u cs
  snarf v cs
snarf (VX a) cs = unpref a cs

unpref :: String -> String -> Maybe String
unpref [] s = return s
unpref (a : as) (c : cs) | a == c = unpref as cs
unpref _ _ = Nothing

txt :: Val -> String
txt (VA a)     = a
txt (VX a)     = a
txt (u :&& v)  = txt u ++ txt v

envBuiltins :: Env
envBuiltins = Empty :/ [DF "plus" [] []
                       ,DF "minus" [] []]

prog :: Env -> [Def Exp] -> Env
prog g ds = g' where
  g' = g :/ map ev ds
  ev (DF f hss pes) = DF f hss pes
  ev (x := e) = x := v where
    Ret v = compute g' e ([], [])

load :: [Def Exp] -> Env
load = prog envBuiltins

loadFile :: String -> IO Env
loadFile x = do
  s <- readFile (x ++ ".uf")
  let Just (d, "") = parse pProg s
  return (prog envBuiltins d)

-- Given env `g` and id `s`,
try :: Env -> String -> Comp
try g s = compute g e ([], []) where
  Just (e, "") = parse pExp s
