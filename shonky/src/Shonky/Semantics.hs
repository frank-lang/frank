module Shonky.Semantics where

import Control.Monad
import Debug.Trace

import Shonky.Syntax

data Val
  = VA String
  | Val :&& Val
  | VX String
  | VF Env [[String]] [([Pat], Exp)]
  | VC Comp
  | VK [Frame]
  deriving Show

data Comp
  = Ret Val
  | Call String [Val] [Frame]
  deriving Show

data Env
  = Env :/ [Def Val]
  | Empty
  deriving Show

data Frame
  = Car Env Exp
  | Cdr Val
  | Fun Env [Exp]
  | Arg [String] Val [Comp] Env [[String]] [Exp]
  | Seq Env Exp
  | Qes Env Exp
  | Qed Val
  | Def Env [Def Val] String [Def Exp] Exp
  | Txt Env [Char] [Either Char Exp]
  deriving Show

fetch :: Env -> String -> Val
fetch g y = go g where
  go h@(g' :/ ds) = defetch ds where
    defetch [] = go g'
    defetch ((x := v) : ds)
      | x == y = v
      | otherwise = defetch ds
    defetch (DF x hss pes : ds)
      | x == y = VF h hss pes
      | otherwise = defetch ds
  go _ = error $ concat ["fetch ",y,show g]

compute :: Env -> Exp -> [Frame] -> Comp
compute g (EV x)       ls = consume (fetch g x) ls
compute g (EA a)       ls = consume (VA a) ls
compute g (a :& d)     ls = compute g a (Car g d : ls)
compute g (f :$ as)    ls = compute g f (Fun g as : ls)
compute g (e :! f)     ls = compute g e (Seq g f : ls)
compute g (e :// f)    ls = compute g e (Qes g f : ls)
compute g (EF hss pes) ls = consume (VF g hss pes) ls
compute g (ds :- e)    ls = define g [] ds e ls
compute g (EX ces)     ls = combine g [] ces ls

consume :: Val -> [Frame] -> Comp
consume v (Car g d             : ls) = compute g d (Cdr v : ls)
consume v (Cdr u               : ls) = consume (u :&& v) ls
consume v (Fun g as            : ls) = args v [] g (handles v) as ls
consume v (Arg _ f cs g hss es : ls) = args f (Ret v : cs) g hss es ls
consume _ (Seq g e             : ls) = compute g e ls
consume v (Qes g e             : ls) = compute g e (Qed v : ls)
consume _ (Qed v               : ls) = consume v ls
consume v (Def g dvs x des e   : ls) = define g ((x := v) : dvs) des e ls
consume v (Txt g cs ces        : ls) = combine g (revapp (txt v) cs) ces ls
consume v []                         = Ret v

revapp :: [x] -> [x] -> [x]
revapp xz ys = foldl (flip (:)) ys xz

combine :: Env -> [Char] -> [Either Char Exp] -> [Frame] -> Comp
combine g cs [] ls = consume (VX (reverse cs)) ls
combine g cs (Left c  : ces) ls = combine g (c : cs) ces ls
combine g cs (Right e : ces) ls = compute g e (Txt g cs ces : ls)

define :: Env -> [Def Val] -> [Def Exp] -> Exp -> [Frame] -> Comp
define g dvs [] e ls = compute (g :/ reverse dvs) e ls
define g dvs (DF f hss pes : des) e ls =
  define g (DF f hss pes : dvs) des e ls
define g dvs ((x := d) : des) e ls =
  compute (g :/ revapp dvs (defo des)) d (Def g dvs x des e : ls)
  where
    defo (DF f hss pes : des) = DF f hss pes : defo des
    defo (_ : des)            = defo des
    defo []                   = []

handles :: Val -> [[String]]
handles (VF _ hss _) = hss
handles _ = []

args :: Val -> [Comp] -> Env -> [[String]] -> [Exp] -> [Frame] -> Comp
args f cs g hss [] ls = apply f (reverse cs) ls
args f cs g [] es ls = args f cs g [[]] es ls
args f cs g (hs : hss) (e : es) ls = compute g e (Arg hs f cs g hss es : ls)

apply :: Val -> [Comp] -> [Frame] -> Comp
apply (VF g _ pes) cs ls = tryRules g pes cs ls
apply (VA a) cs ls = command a (map (\ (Ret v) -> v) cs) [] ls
apply (VC (Ret v)) [] ls = consume v ls
apply (VK ks) [Ret v] ls = consume v (revapp ks ls)
apply f cs ls = error $ concat ["apply: ", show f, show cs, show ls]

command :: String -> [Val] -> [Frame] -> [Frame] -> Comp
command c vs ks [] = Call c vs ks
command c vs ks (Arg hs f cs g hss es : ls)
  | elem c hs = args f (Call c vs ks : cs) g hss es ls
command c vs ks (k : ls) = command c vs (k : ks) ls

tryRules :: Env -> [([Pat], Exp)] -> [Comp] -> [Frame] -> Comp
tryRules g [] cs ls = command "abort" [] [] ls
tryRules g ((ps, e) : pes) cs ls = case matches g ps cs of
  Just g  -> compute g e ls
  Nothing -> tryRules g pes cs ls

matches :: Env -> [Pat] -> [Comp] -> Maybe Env
matches g [] [] = return g
matches g (p : ps) (c : cs) = do
  g <- match g p c
  matches g ps cs
matches _ _ _ = Nothing

match :: Env -> Pat -> Comp -> Maybe Env
match g (PV q) (Ret v) = vmatch g q v
match g (PT x) c = return (g :/ [x := VC c])
match g (PC c qs x) (Call c' vs ks) = do
  guard (c == c')
  g <- vmatches g qs vs
  return (g :/ [x := VK ks])
match _ _ _ = Nothing

vmatches :: Env -> [VPat] -> [Val] -> Maybe Env
vmatches g [] [] = return g
vmatches g (q : qs) (v : vs) = do
  g <- vmatch g q v
  vmatches g qs vs
vmatches _ _ _ = Nothing

vmatch :: Env -> VPat -> Val -> Maybe Env
vmatch g (VPV x) v = return (g :/ [x := v])
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

prog :: Env -> [Def Exp] -> Env
prog g ds = g' where
  g' = g :/ map ev ds
  ev (DF f hss pes) = DF f hss pes
  ev (x := e) = x := v where
    Ret v = compute g' e []

load :: String -> IO Env
load x = do
  s <- readFile (x ++ ".uf")
  let Just (d, "") = parse pProg s
  return (prog Empty d)

try :: Env -> String -> Comp
try g s = compute g e [] where
  Just (e, "") = parse pExp s
