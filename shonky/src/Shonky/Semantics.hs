module Shonky.Semantics where

import Prelude hiding ((<>))

import Control.Monad
import Debug.Trace
import System.IO
import Data.Char
import Data.IORef
import Data.List

import qualified Data.Map.Strict as M

import Shonky.Syntax
import Shonky.Renaming

import Debug.Trace
import Debug

-- There is no predefined Show instance
instance Show (IORef a) where
  show _ = "<ioref>"

data Val
  = VA String                                                               -- atom
  | VI Int                                                                  -- int
  | Val :&& Val                                                             -- cons
  | VX String                                                               -- string
  | VF Env [([Adap], [String])] [([Pat], Exp)]                              -- function (anonymous), has environment, for each port: list of adaptors + list of commands to be captured, list of patterns + handling expressions
  | VB String Env                                                           -- built-in function
  | VC Comp                                                                 -- comp
  | VR (IORef Val)                                                          -- reference cell
  | VK SkippedAgenda                                                        -- continuation
  deriving Show

-- comp: value or command call
data Comp
  = Ret Val                                                                 -- value
  | Call String Int [Val] Agenda                                            -- command call: cmd-id, cmd-level, values, suspended agenda
  deriving Show

-- stack of (collections of definitions)
data Env
  = Env :/ [Def Val]
  | Empty
  deriving Show

data Frame
  = Car Env Exp                                                             -- head can be processed. env, uncomputed tail are recorded
  | Cdr Val                                                                 -- tail can be processed. computed head is recorded
  | Fun Env [Exp]                                                           -- operator can be processed. env, operands are recorded
  | Arg ([Adap], [String]) Val [Comp] Env [([Adap], [String])] [Exp]        -- current arg can be processed.
                                                                            --   ([Adap],     adaptors to be applied on match at current arg
                                                                            --    [String])   handleable commands at current arg
                                                                            --          Val   eval. handler
                                                                            --       [Comp]   eval. args (reversed)
                                                                            --          Env   environment
                                                                            -- [([Adap],      adaptors to be applied at further args
                                                                            --   [String])]   handleable commands at further args
                                                                            --        [Exp]   non-eval. args
  | Seq Env Exp                                                             -- 1st exp can be processed. env, 2nd exp is recorded
  | Qes Env Exp                                                             -- 1st exp can be processed. env, 2nd exp is recorded
  | Qed Val
  | Def Env [Def Val] String [Def Exp] Exp
  | Txt Env [Char] [Either Char Exp]                                        -- current char of string can be processed. env, already computed reversed beginning, rest are recorded
  | Adp Adap                                                                -- adaptor for commands that go below this frame (when looking at the frame stack)
  deriving Show

type Agenda = [Frame]
-- [Frame]: Frame stack (frame first to process is on top)

type SkippedAgenda = [Frame]
-- [Frame]: Skipped frames (most recently skipped frame is on top)

envToList :: Env -> [[Def Val]]
envToList g = envToList' g []
  where envToList' Empty     a = a
        envToList' (g :/ ds) a = envToList' g (ds : a)

-- This pretty-printer more-or-less does the right thing for rendering
-- Frank values encoded in shonky.
--
-- One thing it still gets wrong is printing 'nil' for an empty
-- string, because it does not know the type.
--
-- Another problem is that for complex values (including computations)
-- it resorts to invoking show.

ppVal :: Val -> Doc
ppVal (VA s)  = text $ "'" ++ s   -- TODO: error message here?
ppVal (VI n)  = int n
ppVal v@(VA "cons" :&& (VX [_] :&& _)) = doubleQuotes (ppStringVal v)
ppVal (VA "cons"   :&& (v :&& w))      = ppBrackets $ ppVal v <> ppListVal w
ppVal (VA "nil"    :&& _)              = ppBrackets empty
ppVal (VA k        :&& v)              = text k <> ppConsArgs v
ppVal (VX [c])                         = text $ "'" ++ [c] ++ "'"
ppVal v = text $ "[COMPLEX VALUE: " ++ show v ++ "]"

-- parentheses if necessary
ppValp :: Val -> Doc
ppValp v@(VA "cons" :&& (VX [_] :&& _)) = ppVal v   -- string
ppValp v@(VA _ :&& VA "")               = ppVal v   -- nullary constr.
ppValp v@(VA _ :&& _)                   = ppParens $ ppVal v
ppValp v                                = ppVal v

ppConsArgs :: Val -> Doc
ppConsArgs (v :&& w) = text " " <> ppValp v <> ppConsArgs w
ppConsArgs (VA "")   = text ""
ppConsArgs v         = text "[BROKEN CONSTRUCTOR ARGUMENTS: " <> ppVal v <> text "]"

ppStringVal :: Val -> Doc
ppStringVal (v :&& VA "")                  = ppStringVal v
ppStringVal (VA "cons" :&& (VX [c] :&& v)) = ppChar c <> ppStringVal v
ppStringVal (VA "nil")                     = empty
ppStringVal v                              = text "[BROKEN STRING: " <> ppVal v <> text "]"

ppListVal :: Val -> Doc
ppListVal (v :&& VA "")             = ppListVal v
ppListVal (VA "cons" :&& (v :&& w)) = text ", " <> ppVal v <> ppListVal w
ppListVal (VA "nil")                = text ""
ppListVal v                         = text "[BROKEN LIST: " <> ppVal v <> text "]"

ppAgenda :: Agenda -> Doc
ppAgenda ls = vcat (map ppFrame ls)

ppSkippedAgenda :: SkippedAgenda -> Doc
ppSkippedAgenda ls = vcat (map ppFrame ls)

ppFrame :: Frame -> Doc
ppFrame (Car g e)              = text "Car" <+> ppEnv g <+> ppExp e
ppFrame (Cdr v)                = text "Cdr" <+> ppVal v
ppFrame (Fun g es)             = text "Fun" <+> ppEnv g <+> sep (map ppExp es)
ppFrame (Arg hs f cs g hss es) = text "Arg" <+> nest 3 (vcat [text "hs =" <+> (text . show) hs,
                                                             text "f =" <+> ppVal f,
                                                             text "cs =" <+> nest 3 (vcat $ map ppComp cs),
                                                             text "g =" <+> nest 3 (ppEnv g),
                                                             text "hss =" <+> (text . show) hss,
                                                             text "es" <+> nest 3 (vcat $ map ppExp es)])
ppFrame (Seq g e)              = text "Seq" <+> ppEnv g <+> ppExp e
ppFrame (Qes g e)              = text "Qes" <+> ppEnv g <+> ppExp e
ppFrame (Qed v)                = text "Qed" <+> ppVal v
ppFrame (Adp (cs, r))          = text "Adp" <+> text "[" <+> (hcat $ punctuate comma (map text cs)) <+> text "]" <+> (text . show) r

ppEnv :: Env -> Doc
ppEnv g = bracketed empty (map ((bracketed (text "\n")) . (map ppDefVal)) (envToList g))

ppDefVal :: Def Val -> Doc
ppDefVal (x := v)      = text x <+> text "->" <+> ppVal v
ppDefVal (DF f [] [])  = text f <+> text "->" <+> text "[empty function]"
ppDefVal (DF f xs ys)  = ppDef (DF f xs ys)

ppComp :: Comp -> Doc
ppComp (Ret v)         = text "Ret" <+> ppVal v
ppComp (Call c n vs a) = text "Call" <+> text c <> text "." <> int n <+> sep (map ppVal vs) $$ ppAgenda a

sepBy :: Doc -> [Doc] -> Doc
sepBy s ds = vcat $ punctuate s ds

bracketed :: Doc -> [Doc] -> Doc
bracketed s ds = lbrack <+> (sepBy s ds <+> rbrack)

-- Given env and 2 operands (that are values), compute result
plus :: Env -> [Comp] -> Val
plus g [a1,a2] = VI (f a1 + f a2)
  where f x = case x of
          Ret (VI n) -> n
          _ -> error "plus: argument not an int"
plus g _ = error "plus: incorrect number of arguments, expected 2."

minus :: Env -> [Comp] -> Val
minus g [a1,a2] = VI (f a1 - f a2)
  where f x = case x of
          Ret (VI n) -> n
          _ -> error "minus: argument not an int"
minus g _ = error "minus: incorrect number of arguments, expected 2."

builtinPred :: Bool -> Val
builtinPred b = (if b then VA "true" else VA "false") :&& VA ""

lt :: Env -> [Comp] -> Val
lt g [a1,a2] = builtinPred ((f a1) < (f a2))
  where f x = case x of
          Ret (VI n) -> n
          _ -> error "plus: argument not an int"
lt g _ = error "plus: incorrect number of arguments, expected 2."

gt :: Env -> [Comp] -> Val
gt g [a1,a2] = builtinPred ((f a1) > (f a2))
  where f x = case x of
          Ret (VI n) -> n
          _ -> error "plus: argument not an int"
gt g _ = error "plus: incorrect number of arguments, expected 2."


eqc :: Env -> [Comp] -> Val
eqc g [a1,a2] = builtinPred ((f a1) == (f a2))
  where f x = case x of
          Ret (VX [c]) -> c
          _ -> error "eqc: argument not a character"
eqc g _ = error "eqc: incorrect number of arguments, expected 2."

alphaNumPred :: Env -> [Comp] -> Val
alphaNumPred g [a] =
  (if isAlphaNum (f a) then VA "true" else VA "false") :&& VA ""
  where f x = case x of
          Ret (VX [c]) -> c
          _ -> error "alphaNumPred: argument not a character"
alphaNumPred g _ =
  error "alphaNumPred: incorrect number of arguments, expected 2."


builtins :: M.Map String (Env -> [Comp] -> Val)
builtins = M.fromList [("plus", plus), ("minus", minus), ("eqc", eqc)
                      ,("lt", lt), ("gt", gt)
                      ,("isAlphaNum", alphaNumPred)]

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

-- High-level computation functions that return a Comp (either Val or
-- command call):
--   compute, consume, define, combine, args, command, tryRules
-- Most of them take an Env and maintain an agenda (frame stack,
-- commands-to-be-skipped).

-- Given env `g` and framestack `ls`, compute expression.
-- 1) Terminating exp: Feed value into top frame
-- 2) Ongoing exp:     Create new frame
compute :: Env -> Exp -> Agenda -> Comp
compute g (EV x)       ls   = consume (fetch g x) ls                        -- 1) look-up value
compute g (EA a)       ls   = consume (VA a) ls                             -- 1) feed atom
compute g (EI n)       ls   = consume (VI n) ls                             -- 1) feed int
compute g (a :& d)     ls   = compute g a (Car g d : ls)                    -- 2) compute head. save tail for later.
compute g (f :$ as)    ls   = compute g f (Fun g as : ls)                   -- 2) Application. Compute function. Save args for later.
compute g (e :! f)     ls   = compute g e (Seq g f : ls)                    -- 2) Sequence.    Compute 1st exp.  Save 2nd for later.
compute g (e :// f)    ls   = compute g e (Qes g f : ls)                    -- 2) Composition. Compute 1st exp.  save 2nd for later.
compute g (EF hss pes) ls   = consume (VF g hss pes) ls                     -- 1) feed in function
compute g (ds :- e)    ls   = define g [] ds e ls                           -- (not used by Frank)
compute g (EX ces)     ls   = combine g [] ces ls                           -- 2) compute string
compute g (ER (cs, r) e) ls = compute g e (Adp (cs, r) : ls)                -- 2) add commands to be skipped in `ls`

-- Take val `v` and top-frame from stack, apply it to `v` in
consume :: Val -> Agenda -> Comp
consume v (Car g d    : ls) = compute g d (Cdr v : ls)                      -- Given: eval. head `v`,     non-eval. tail `d`.  Record `v` and compute tail `d`.
consume v (Cdr u      : ls) = consume (simplStr u v) (ls)                   -- Given: eval. head `u`,     eval.     tail `v`.  Put together.
consume v (Fun g as   : ls) = args v [] g (adapsAndHandles v) as (ls)       -- Given: eval. function `v`, non-eval. args `as`. Compute `as`, then feed them into `v`
consume v (Arg _ f cs g
               hss es : ls) = args f (Ret v : cs) g hss es (ls)             -- Given: Eval.:     handler `f`,
                                                                                      --                   first args `cs` (reversed),
                                                                                      --                   current arg `v`
                                                                                      --        Non-eval.: last args `es`
                                                                                      -- Add `v` to `cs` and re-call `args`
consume _ (Seq g e           : ls) = compute g e (ls)                       -- Sequence.    Given: eval. 1st _,   non-eval. 2nd `e`. Compute `e`.
consume v (Qes g e           : ls) = compute g e (Qed v : ls)               -- Composition. Given: eval. 1st `v`, non-eval. 2nd `e`. Record `v` and compute `e`.
consume _ (Qed v             : ls) = consume v (ls)                         -- LC: Bug here? Why discard argument? (but not used by Frank so far anyway)
consume v (Def g dvs x des e : ls) = define g ((x := v) : dvs) des e (ls)   -- (not used by Frank)
consume v (Txt g cs ces      : ls) = combine g (revapp (txt v) cs) ces (ls) -- (not used by Frank)
consume v (Adp (cs, r)       : ls) = consume v ls                           -- ignore addaptor when value is obtained
consume v []                       = Ret v

-- inch, ouch, inint and ouint commands in the IO monad
-- only if the level is 0 --TODO LC: rethink this?
ioHandler :: Comp -> IO Val
ioHandler (Ret v) = return v
ioHandler (Call "inch" 0 [] ks) =
  do c <- getChar
     -- HACK: for some reason backspace seems to produce '\DEL' instead of '\b'
     let c' = if c == '\DEL' then '\b' else c
     ioHandler (consume (VX [c']) (reverse ks))
ioHandler comp@(Call "ouch" 0 [VX [c]] ks) =
  do putChar c
     hFlush stdout
     ioHandler (consume (VA "unit" :&& VA "") (reverse ks))
ioHandler comp@(Call "ouint" 0 [VI k] ks) =
  do putStr (show k)
     hFlush stdout
     ioHandler (consume (VA "unit" :&& VA "") (reverse ks))
ioHandler (Call "new" 0 [v] ks) =
  do ref <- newIORef v
     ioHandler (consume (VR ref) (reverse ks))
ioHandler (Call "write" 0 [VR ref, v] ks) =
  do writeIORef ref v
     ioHandler (consume (VA "unit" :&& VA "") (reverse ks))
ioHandler (Call "read" 0 [VR ref] ks) =
  do v <- readIORef ref
     ioHandler (consume v (reverse ks))
ioHandler (Call c n vs ks) = error $ "Unhandled command: " ++ c ++ "." ++
                                     show n ++ concat (map (\v -> " " ++
                                    (show . ppVal) v) vs)

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

-- evaluate string of type [Either Char Exp]
-- given: env, already computed reversed beginning, rest, frame stack
combine :: Env -> [Char] -> [Either Char Exp] -> Agenda -> Comp
combine g cs [] ls = consume (VX (reverse cs)) ls
combine g cs (Left c  : ces) ls = combine g (c : cs) ces ls
combine g cs (Right e : ces) ls = compute g e (Txt g cs ces : ls)

-- (not used in Frank)
define :: Env -> [Def Val] -> [Def Exp] -> Exp -> Agenda -> Comp
define g dvs [] e ls = compute (g :/ reverse dvs) e ls
define g dvs (DF f hss pes : des) e ls =
  define g (DF f hss pes : dvs) des e ls
define g dvs ((x := d) : des) e ls =
  compute (g :/ revapp dvs (defo des)) d (Def g dvs x des e : ls)
  where
    defo (DF f hss pes : des) = DF f hss pes : defo des
    defo (_ : des)            = defo des
    defo []                   = []

-- Return adaptors and handleable commands
adapsAndHandles :: Val -> [([Adap], [String])]
adapsAndHandles (VF _ hss _) = hss
adapsAndHandles _ = []

-- given: eval. operator `f`, eval. reversed arguments `cs`, env `g`,
--        handleable commands, non-eval. args `es`, frame stack
-- Compute until all [Exp] are [Comp], then call `apply`.
args :: Val -> [Comp] -> Env -> [([Adap], [String])] -> [Exp] -> Agenda -> Comp
args f cs g hss [] ls = apply f (reverse cs) ls                             -- apply when all args are evaluated
args f cs g [] es ls = args f cs g [([], [])] es ls                         -- default to [] (no handleable commands) if not explicit
args f cs g (hs : hss) (e : es) ls = compute g e
                                             (Arg hs f cs g hss es : ls)    -- compute argument, record rest. will return eventually here.
-- TODO: LC: remove and fix the second case of args (it's a bit of a hack right now)

-- `apply` is called by `args` when all arguments are evaluated
-- given: eval. operator, eval. args, frame stack
apply :: Val -> [Comp] -> Agenda -> Comp
apply (VF g _ pes) cs ls = tryRules g pes cs ls                             -- apply function to evaluated args `cs`
apply (VB x g) cs ls = case M.lookup x builtins of                          -- apply built-in fct. to evaluated args `cs`
  Just f -> consume (f g cs) ls
  Nothing -> error $ concat ["apply: ", x, " not a builtin"]
apply (VA a) cs ls =                                                        -- apply a command to evaluated args `cs`
  -- commands are not handlers, so the cs must all be values
  command a (map (\ (Ret v) -> v) cs) [] 0 ls
apply (VC (Ret v)) [] ls = consume v ls                                     -- apply a value-thunk to 0 args (force)
apply (VC (Call a n vs ks)) [] ls = command a vs ks n ls                    -- apply a command-thunk to 0 args (force), `n` determines how many handlers to skip
apply (VK sag) [Ret v] ag = consume v (revapp sag ag)                       -- execute a continuation by providing return value:
apply f cs ls = error $ concat ["apply: ", show f, show cs, show ls]

-- given:
--    c:  cmd-id
--    vs: evaluated args
--    ks: skipped agenda
--    n:  levels to skip
--    ls: current agenda
-- Assign command-request to a handler (fix argument) and continue with `args`.
-- If there is no handler, just return a `Call` (comp. is stuck)
--   cas: commands-already-skipped
--   cts: commands-to-be-skipped
command :: String -> [Val] -> SkippedAgenda -> Int -> Agenda -> Comp
command c vs ks n [] = Call c n vs ks                                       -- if agenda is done (i.e. no handler there), return Call
command c vs ks n (k@(Arg (adps, hs) f cs g hss es) : ls) =                 -- if there is a handler...
   let n' = applyAdaptorsToCommand adps c n in -- apply adaptors in any case
   let count = length (filter (== c) hs) in
   if n' < count then args f (Call c n' vs ks : cs) g hss es ls             -- ... that can handle `c`:    handle it
                 else command c vs (k : ks) (n'-count) ls                   -- ... that cannot handle `c`: recurse
  where applyAdaptorsToCommand :: [Adap] -> String -> Int -> Int
        applyAdaptorsToCommand [] c n = n
        applyAdaptorsToCommand (a:ar) c n = applyAdaptorsToCommand ar c (applyAdaptorToCommand a c n)
        applyAdaptorToCommand :: Adap -> String -> Int -> Int
        applyAdaptorToCommand (cs, ren) c n = if c `elem` cs
                                                then renToFun ren n
                                                else n
command c vs ks n (Adp (cs, r) : ls)
  | c `elem` cs = command c vs (Adp (cs, r) : ks) (renToFun r n) ls         -- if there is an adaptor frame: apply adaptor and recurse
command c vs ks n (k : ls) = command c vs (k : ks) n ls                     -- skip current handler `k` and recurse

-- given:  env, rules, evaluated args, frame stack
-- selects first rule that matches and computes that expression
tryRules :: Env -> [([Pat], Exp)] -> [Comp] -> Agenda -> Comp
tryRules g [] cs ls = command "abort" [] [] 0 ls                            -- no rule matches
tryRules g ((ps, e) : pes) cs ls = case matches g ps cs of
  Just g  -> compute g e ls                                                 -- rule matches, compute
  Nothing -> tryRules g pes cs ls                                           -- rule fails, try next

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
match g (PV q) (Ret v) = vmatch g q v                                       -- value matching, no binding
match g (PT x) c = return (g :/ [x := VC c])                                -- variable binding
match g (PC c n qs x) (Call c' n' vs ks) = do                               -- command call matching: cmd parameters `vs`, continuation (future agenda)
  guard (c == c')
  guard (n == n')
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
                       ,DF "minus" [] []
                       ,DF "eqc"   [] []
                       ,DF "gt"    [] []
                       ,DF "lt"    [] []]

prog :: Env -> [Def Exp] -> Env
prog g ds = g' where
  g' = g :/ map ev ds
  ev (DF f hss pes) = DF f hss pes
  ev (x := e) = x := v where
    Ret v = compute g' e []

load :: [Def Exp] -> Env
load = prog envBuiltins

loadFile :: String -> IO Env
loadFile x = do
  s <- readFile (x ++ ".uf")
  let Just (d, rest) = parse pProg s
  traceM $ "parsed:\n\n" ++ (show $ vsep (map ppDef d)) ++ "\n\n"
  traceM $ "rest: \n\n" ++ (show rest)
  return (prog envBuiltins d)

-- Given env `g` and id `s`,
try :: Env -> String -> Comp
try g s = compute g e [] where
  Just (e, "") = parse pExp s
